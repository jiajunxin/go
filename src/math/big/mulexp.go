package big

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
	for i := 2; i < 1<<n; i++ {
		powers[i] = powers[i].montgomery(powers[i-1], powers[1], m, k0, numWords)
	}

	// initialize z1, z2 = 1 (Montgomery 1)
	var z1, z2, zz2 nat
	z1 = z1.make(numWords)
	z2 = z2.make(numWords)
	copy(z1, powers[0])
	copy(z2, powers[0])

	zz1 = zz1.make(numWords)
	copy(zz2, zz1)

	// // same windowed exponent, but with Montgomery multiplications
	// for i := len(y1) - 1; i >= 0; i-- {
	// 	yi := y1[i]
	// 	for j := 0; j < _W; j += n {
	// 		if i != len(y1)-1 || j != 0 {
	// 			zz1 = zz1.montgomery(z1, z1, m, k0, numWords)
	// 			z1 = z1.montgomery(zz1, zz1, m, k0, numWords)
	// 			zz1 = zz1.montgomery(z1, z1, m, k0, numWords)
	// 			z1 = z1.montgomery(zz1, zz1, m, k0, numWords)
	// 		}
	// 		zz1 = zz1.montgomery(z1, powers[yi>>(_W-n)], m, k0, numWords)
	// 		z1, zz1 = zz1, z1
	// 		yi <<= n
	// 	}
	// }
	// // convert to regular number
	// zz1 = zz1.montgomery(z1, one, m, k0, numWords)
	var squaredPower nat
	copy(squaredPower, powers[1])
	for i := 0; i < len(y1); i++ {
		for j := 0; j < _W; j++ {
			mask := Word(1 << j)
			if (y1[i] & mask) == mask {
				z1 = z1.montgomery(z1, squaredPower, m, k0, numWords)
			}
			squaredPower = squaredPower.montgomery(squaredPower, squaredPower, m, k0, numWords)
		}
	}

	// One last reduction, just in case.
	// See golang.org/issue/13907.
	if z1.cmp(m) >= 0 {
		// Common case is m has high bit set; in that case,
		// since zz is the same length as m, there can be just
		// one multiple of m to remove. Just subtract.
		// We think that the subtract should be sufficient in general,
		// so do that unconditionally, but double-check,
		// in case our beliefs are wrong.
		// The div is not expected to be reached.
		z1 = z1.sub(z1, m)
		if z1.cmp(m) >= 0 {
			_, z1 = nat(nil).div(nil, z1, m)
		}
	}
	z1.norm()
	//zz2.norm()
	var ret1, ret2 Int
	ret1.abs = z1
	ret2.abs = zz2
	ret1.neg = false
	ret2.neg = false
	return []*Int{&ret1, &ret2}
}
