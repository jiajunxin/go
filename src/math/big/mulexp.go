package big

import (
	"fmt"
)

// MultiExp sets z1 = x**y1 mod |m|, z2 = x**y2 mod |m| ... (i.e. the sign of m is ignored), and returns z1, z2.
// If m == nil or m == 0, z = x**y unless y <= 0 then z = 1. If m != 0, y < 0,
// and x and m are not relatively prime, z is unchanged and nil is returned.
//
// MultiExp is not a cryptographically constant-time operation.
func MultiExp(x, y1, y2, m *Int) []*Int {
	// See Knuth, volume 2, section 4.6.3.
	var z1, z2 Int
	ret := make([]*Int, 2)
	ret[0] = &z1
	ret[1] = &z2

	xWords := x.abs
	if len(xWords) == 0 {
		z1.SetInt64(1)
		z2.SetInt64(1)
		return ret
	}
	if x.neg || y1.neg || y2.neg || m.neg {
		z1.Exp(x, y2, m)
		z2.Exp(x, y2, m)
		return ret
	}
	if len(xWords) == 1 && xWords[0] == 1 {
		z1.SetInt64(1)
		z2.SetInt64(1)
		return ret
	}

	// x > 1

	if m == nil {
		z1.SetInt64(1)
		z2.SetInt64(1)
		return ret
	}
	mWords := m.abs // m.abs may be nil for m == 0
	if len(mWords) == 0 {
		z1.SetInt64(1)
		z2.SetInt64(1)
		return ret
	}
	// m > 1
	y1Words := y1.abs
	y2Words := y2.abs

	// x**0 == 1
	if len(y1Words) == 0 {
		if len(y2Words) == 0 {
			z1.SetInt64(1)
			z2.SetInt64(1)
			return ret
		}
		z1.SetInt64(1)
		z2.Exp(x, y2, m)
		return ret
	}
	if len(y2Words) == 0 {
		z2.SetInt64(1)
		z1.Exp(x, y1, m)
		return ret
	}
	// y > 0

	// x**1 == x
	if len(y1Words) == 1 && y1Words[0] == 1 {
		if len(y2Words) == 1 && y2Words[0] == 1 {
			z1.abs.rem(x.abs, m.abs)
			z2.abs.rem(x.abs, m.abs)
			return ret
		}
		y1Words.rem(x.abs, m.abs)
		z2.Exp(x, y2, m)
		return ret
	}
	if len(y2Words) == 1 && y2Words[0] == 1 {
		y2Words.rem(x.abs, m.abs)
		z1.Exp(x, y1, m)
		return ret
	}
	// y > 1

	// If the exponent is large, we use the Montgomery method for odd values,
	// and a 4-bit, windowed exponentiation for powers of two,
	// and a CRT-decomposed Montgomery method for the remaining values
	// (even values times non-trivial odd values, which decompose into one
	// instance of each of the first two cases).
	if mWords[0]&1 == 1 {
		return multiexpNNMontgomery(xWords, y1Words, y2Words, mWords)
	}

	z1.abs.rem(x.abs, m.abs)
	z2.abs.rem(x.abs, m.abs)
	return ret
}

// multiexpNNMontgomery calculates x**y1 mod m and x**y2 mod m using a fixed, 4-bit window.
// Uses Montgomery representation.
func multiexpNNMontgomery(x, y1, y2, m nat) []*Int {
	numWords := len(m)

	// We want the lengths of x and m to be equal.
	// It is OK if x >= m as long as len(x) == len(m).
	if len(x) > numWords {
		_, x = nat(nil).div(nil, x, m)
		// Note: now len(x) <= numWords, not guaranteed ==.
	}
	if len(x) < numWords {
		rr := make(nat, numWords)
		copy(rr, x)
		x = rr
	}

	// Ideally the precomputations would be performed outside, and reused
	// k0 = -m**-1 mod 2**_W. Algorithm from: Dumas, J.G. "On Newton–Raphson
	// Iteration for Multiplicative Inverses Modulo Prime Powers".
	k0 := 2 - m[0]
	t := m[0] - 1
	for i := 1; i < _W; i <<= 1 {
		t *= t
		k0 *= (t + 1)
	}
	k0 = -k0

	// RR = 2**(2*_W*len(m)) mod m
	RR := nat(nil).setWord(1)
	zz1 := nat(nil).shl(RR, uint(2*numWords*_W))
	_, RR = nat(nil).div(RR, zz1, m)
	if len(RR) < numWords {
		zz1 = zz1.make(numWords)
		copy(zz1, RR)
		RR = zz1
	}

	// one = 1, with equal length to that of m
	one := make(nat, numWords)
	one[0] = 1

	const n = 4
	// powers[i] contains x^i
	var powers [1 << n]nat
	powers[0] = powers[0].montgomery(one, RR, m, k0, numWords)
	powers[1] = powers[1].montgomery(x, RR, m, k0, numWords)

	return multimontgomery(RR, m, powers[0], powers[1], k0, numWords, []nat{y1, y2})
	// for i := 2; i < 1<<n; i++ {
	// 	powers[i] = powers[i].montgomery(powers[i-1], powers[1], m, k0, numWords)
	// }
	// fmt.Println("RR = ", RR.String())
	// fmt.Println("powers[0] = ", powers[0].String())
	// fmt.Println("powers[1] = ", powers[1].String())
	// // initialize z1, z2 = 1 (Montgomery 1)
	// var z1, z2, zz2, zcom, zzcom nat
	// z1 = z1.make(numWords)
	// z2 = z2.make(numWords)
	// zcom = zcom.make(numWords)
	// copy(z1, powers[0])
	// copy(z2, powers[0])
	// copy(zcom, powers[0])
	// fmt.Println("z1 = ", z1.String())

	// zz1 = zz1.make(numWords)
	// zz2 = zz2.make(numWords)
	// zzcom = zzcom.make(numWords)
	// copy(zz2, zz1)
	// copy(zzcom, zz1)

	// fmt.Println("test in big.Int")
	// var squaredPower, temp nat
	// squaredPower = squaredPower.make(numWords)
	// temp = temp.make(numWords)
	// copy(squaredPower, powers[1])
	// fmt.Println("squaredPower = ", squaredPower.String())
	// fmt.Println("temp = ", temp.String())
	// fmt.Println("len(y1) = ", len(y1))
	// for i := 0; i < len(y1); i++ {
	// 	for j := 0; j < _W; j++ {
	// 		mask := Word(1 << j)
	// 		if (y1[i] & mask) == mask {
	// 			// montgomery must have the returned value not same as the input values
	// 			// we have to use this temp as the middle variable
	// 			temp = temp.montgomery(z1, squaredPower, m, k0, numWords)
	// 			z1, temp = temp, z1
	// 		}
	// 		temp = temp.montgomery(squaredPower, squaredPower, m, k0, numWords)
	// 		squaredPower, temp = temp, squaredPower
	// 	}
	// }
	// // convert to regular number
	// temp = temp.montgomery(z1, one, m, k0, numWords)
	// z1, temp = temp, z1
	// fmt.Println("squaredPower = ", squaredPower.String())
	// fmt.Println("temp = ", temp.String())
	// fmt.Println("ret1 = ", z1.String())
	// // One last reduction, just in case.
	// // See golang.org/issue/13907.
	// if z1.cmp(m) >= 0 {
	// 	// Common case is m has high bit set; in that case,
	// 	// since zz is the same length as m, there can be just
	// 	// one multiple of m to remove. Just subtract.
	// 	// We think that the subtract should be sufficient in general,
	// 	// so do that unconditionally, but double-check,
	// 	// in case our beliefs are wrong.
	// 	// The div is not expected to be reached.
	// 	z1 = z1.sub(z1, m)
	// 	if z1.cmp(m) >= 0 {
	// 		_, z1 = nat(nil).div(nil, z1, m)
	// 	}
	// }
	// fmt.Println("ret1 = ", z1.String())
	// z1.norm()
	// //zz2.norm()
	// var ret1, ret2 Int
	// ret1.abs = z1
	// ret2.abs = zz2
	// fmt.Println("ret1 = ", z1.String())
	// ret1.neg = false
	// ret2.neg = false

	// return []*Int{&ret1, &ret2}
}

func multimontgomery(RR, m, power0, power1 nat, k0 Word, numWords int, y []nat) []*Int {
	ret := make([]*Int, len(y))
	for i := range ret {
		ret[i] = new(Int)
	}

	// initialize each value to be 1 (Montgomery 1)
	z := make([]nat, len(y))
	for i := range ret {
		z[i] = z[i].make(numWords)
		copy(z[i], power0)
	}

	fmt.Println("test in big.Int")
	var squaredPower, temp nat
	squaredPower = squaredPower.make(numWords)
	temp = temp.make(numWords)
	copy(squaredPower, power1)
	fmt.Println("squaredPower = ", squaredPower.String())
	fmt.Println("temp = ", temp.String())
	fmt.Println("len(y[0]) = ", len(y[0]))

	maxLen := 1
	for i := range y {
		if len(y[i]) > maxLen {
			maxLen = len(y[i])
		}
	}

	for i := 0; i < maxLen; i++ {
		for j := 0; j < _W; j++ {
			mask := Word(1 << j)
			for k := range y {
				if len(y[k]) > i {
					if (y[k][i] & mask) == mask {
						temp = temp.montgomery(z[k], squaredPower, m, k0, numWords)
						z[k], temp = temp, z[k]
					}
				}
			}
			// montgomery must have the returned value not same as the input values
			// we have to use this temp as the middle variable
			temp = temp.montgomery(squaredPower, squaredPower, m, k0, numWords)
			squaredPower, temp = temp, squaredPower
		}
	}
	// one = 1, with equal length to that of m
	one := make(nat, numWords)
	one[0] = 1
	// convert to regular number
	for i := range z {
		temp = temp.montgomery(z[i], one, m, k0, numWords)
		z[i], temp = temp, z[i]
	}
	fmt.Println("squaredPower = ", squaredPower.String())
	fmt.Println("temp = ", temp.String())
	for i := range z {
		// One last reduction, just in case.
		// See golang.org/issue/13907.
		if z[i].cmp(m) >= 0 {
			// Common case is m has high bit set; in that case,
			// since zz is the same length as m, there can be just
			// one multiple of m to remove. Just subtract.
			// We think that the subtract should be sufficient in general,
			// so do that unconditionally, but double-check,
			// in case our beliefs are wrong.
			// The div is not expected to be reached.
			z[i] = z[i].sub(z[i], m)
			if z[i].cmp(m) >= 0 {
				_, z[i] = nat(nil).div(nil, z[i], m)
			}
		}
	}

	// normlize and set value
	for i := range z {
		z[i].norm()
		ret[i].abs = z[i]
		ret[i].neg = false
	}
	return ret
}

func GCB(a, b nat) nat {
	var maxBitLen int
	if len(a) > len(b) {
		maxBitLen = len(b)
	} else {
		maxBitLen = len(a)
	}
	fmt.Println("test 0 ")
	var bitStingsRet nat

	bitStingsRet = bitStingsRet.make(maxBitLen)
	for i := 0; i < maxBitLen; i++ {
		bitStingsRet[i] = CommonBits(a[i], b[i])
		a[i] = a[i] - bitStingsRet[i]
		b[i] = b[i] - bitStingsRet[i]
	}
	return bitStingsRet
}

func CommonBits(a, b Word) Word {
	var ret uint
	ret = 0
	var mask uint
	for i := 0; i < 32; i++ {
		mask = uint(1 << i)
		if ((uint(a) & mask) == mask) && ((uint(b) & mask) == mask) {
			//fmt.Println("i == ", i, "mask = ", mask)
			ret = uint(ret) | mask
		}
	}

	return Word(ret)
}
