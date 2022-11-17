package big

// DoubleExp sets z1 = x**y1 mod |m|, z2 = x**y2 mod |m| ... (i.e. the sign of m is ignored), and returns z1, z2.
// If m == nil or m == 0, z = x**y unless y <= 0 then z = 1. If m != 0, y < 0,
// and x and m are not relatively prime, z is unchanged and nil is returned.
//
// DoubleExp is not a cryptographically constant-time operation.
func DoubleExp(x, y1, y2, m *Int) []*Int {
	// See Knuth, volume 2, section 4.6.3.
	var z1, z2 Int
	ret := make([]*Int, 2)
	ret[0] = &z1
	ret[1] = &z2

	xWords := x.abs
	if len(xWords) == 0 {
		return allIntOne(2)
	}
	if x.neg || y1.neg || y2.neg || m.neg {
		z1.Exp(x, y2, m)
		z2.Exp(x, y2, m)
		return ret
	}
	if len(xWords) == 1 && xWords[0] == 1 {
		return allIntOne(2)
	}

	// x > 1

	if m == nil {
		return allIntOne(2)
	}
	mWords := m.abs // m.abs may be nil for m == 0
	if len(mWords) == 0 {
		return allIntOne(2)
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

	if mWords[0]&1 == 1 {
		return doubleexpNNMontgomery(xWords, y1Words, y2Words, mWords)
	}

	z1.abs.rem(x.abs, m.abs)
	z2.abs.rem(x.abs, m.abs)
	return ret
}

// allIntOne inputs a slice length and returns a slice of *Int, with all values "1"
func allIntOne(length int) []*Int {
	ret := make([]*Int, length)
	for i := range ret {
		ret[i] = new(Int)
		ret[i].SetInt64(1)
	}
	return ret
}

// doubleexpNNMontgomery calculates x**y1 mod m and x**y2 mod m
// Uses Montgomery representation.
func doubleexpNNMontgomery(x, y1, y2, m nat) []*Int {
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

	// powers[i] contains x^i
	var powers [2]nat
	powers[0] = powers[0].montgomery(one, RR, m, k0, numWords)
	powers[1] = powers[1].montgomery(x, RR, m, k0, numWords)

	y1New, y2New, y3 := gcb(y1, y2)
	z := multimontgomery(RR, m, powers[0], powers[1], k0, numWords, []nat{y1New, y2New, y3})
	// calculate z1 and z2
	var temp nat
	temp = temp.make(numWords)
	temp = temp.montgomery(z[0], z[2], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[1], z[2], m, k0, numWords)
	z[1], temp = temp, z[1]
	z = z[:2] //z3 is useless now
	// convert to regular number
	for i := range z {
		temp = temp.montgomery(z[i], one, m, k0, numWords)
		z[i], temp = temp, z[i]
	}
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

	ret := make([]*Int, 2)
	for i := range ret {
		ret[i] = new(Int)
	}

	// normlize and set value
	for i := range z {
		z[i].norm()
		ret[i].abs = z[i]
		ret[i].neg = false
	}
	return ret
}

// multimontgomery calculates the modular montgomery exponent with result not normlized
func multimontgomery(RR, m, power0, power1 nat, k0 Word, numWords int, y []nat) []nat {
	// initialize each value to be 1 (Montgomery 1)
	z := make([]nat, len(y))
	for i := range z {
		z[i] = z[i].make(numWords)
		copy(z[i], power0)
	}

	var squaredPower, temp nat
	squaredPower = squaredPower.make(numWords)
	temp = temp.make(numWords)
	copy(squaredPower, power1)
	//fmt.Println("squaredPower = ", squaredPower.String())

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
	return z
}

// GCB inputs two positive integer a and b, calculates the greatest common
func gcb(a, b nat) (nat, nat, nat) {
	var maxBitLen int
	if len(a) > len(b) {
		maxBitLen = len(b)
	} else {
		maxBitLen = len(a)
	}
	var aNew, bNew, c nat

	aNew = aNew.make(maxBitLen)
	bNew = bNew.make(maxBitLen)
	c = c.make(maxBitLen)
	for i := 0; i < maxBitLen; i++ {
		c[i] = commonBits(a[i], b[i])
		aNew[i] = a[i] - c[i]
		bNew[i] = b[i] - c[i]
	}
	return aNew, bNew, c
}

// fourfoldGcb inputs four positive integer a, b, c, d and calculates the greatest common
// the last element in output is the common bits integer
func fourfoldGcb(input []nat) []nat {
	if len(input) != 4 {
		panic("fourfoldGcb require the input size to be 4")
	}
	maxBitLen := 0
	minBitLen := len(input[0])
	for i := 0; i < 4; i++ {
		if maxBitLen < len(input[i]) {
			maxBitLen = len(input[i])
		}
		if minBitLen > len(input[i]) {
			minBitLen = len(input[i])
		}
	}

	var output [5]nat
	for i := 0; i < 4; i++ {
		output[i] = output[i].make(len(input[i]))
	}
	output[4] = output[4].make(minBitLen)
	for i := 0; i < minBitLen; i++ {
		output[4][i] = fourfoldCommonBits(input[0][i], input[1][i], input[2][i], input[3][i])
		output[0][i] = input[0][i] - output[4][i]
		output[1][i] = input[1][i] - output[4][i]
		output[2][i] = input[2][i] - output[4][i]
		output[3][i] = input[3][i] - output[4][i]
	}
	return output[:]
}

// threefoldGcb inputs three positive integer a, b, c and calculates the greatest common
// the last element in output is the common bits integer
func threefoldGcb(input []nat) nat {
	if len(input) != 3 {
		panic("threefoldGcb require the input size to be 3")
	}
	maxBitLen := 0
	minBitLen := len(input[0])
	for i := 0; i < 3; i++ {
		if maxBitLen < len(input[i]) {
			maxBitLen = len(input[i])
		}
		if minBitLen > len(input[i]) {
			minBitLen = len(input[i])
		}
	}

	var output nat
	output = output.make(minBitLen)
	for i := 0; i < minBitLen; i++ {
		output[i] = threefoldCommonBits(input[0][i], input[1][i], input[2][i])
		input[0][i] = input[0][i] - output[i]
		input[1][i] = input[1][i] - output[i]
		input[2][i] = input[2][i] - output[i]
	}
	return output[:]
}

func commonBits(a, b Word) Word {
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

func threefoldCommonBits(a, b, c Word) Word {
	var ret uint
	ret = 0
	var mask uint
	for i := 0; i < 32; i++ {
		mask = uint(1 << i)
		if ((uint(a) & mask) == mask) && ((uint(b) & mask) == mask) && ((uint(c) & mask) == mask) {
			ret = uint(ret) | mask
		}
	}
	return Word(ret)
}

func fourfoldCommonBits(a, b, c, d Word) Word {
	var ret uint
	ret = 0
	var mask uint
	for i := 0; i < 32; i++ {
		mask = uint(1 << i)
		if ((uint(a) & mask) == mask) && ((uint(b) & mask) == mask) && ((uint(c) & mask) == mask) && ((uint(d) & mask) == mask) {
			ret = uint(ret) | mask
		}
	}
	return Word(ret)
}

// FourFoldExp sets z1 = x**y1 mod |m|, z2 = x**y2 mod |m| ... (i.e. the sign of m is ignored), and returns z1, z2...
// In construction, many panic conditions. Use at your own risk!
//
// FourFoldExp is not a cryptographically constant-time operation.
func FourFoldExp(x, m *Int, y []*Int) []*Int {
	xWords := x.abs
	if len(xWords) == 0 {
		return allIntOne(4)
	}
	if x.neg || m.neg {
		panic("negative x or m as input for MultiExp")
	}
	if len(y)%2 != 0 {
		panic("MultiExp does not support odd length of y for now!")
	}
	for i := range y {
		if y[i].neg {
			panic("negative y[i] as input for MultiExp")
		}
	}
	if len(xWords) == 1 && xWords[0] == 1 {
		return allIntOne(len(y))
	}

	// x > 1

	if m == nil {
		return allIntOne(len(y))
	}
	mWords := m.abs // m.abs may be nil for m == 0
	if len(mWords) == 0 {
		return allIntOne(len(y))
	}
	// m > 1
	// y > 0

	if mWords[0]&1 != 1 {
		panic("The input modular is not a odd number")
	}
	return fourfoldExpNNMontgomery(xWords, mWords, y)
}

// fourfoldExpNNMontgomery calculates x**y1 mod m and x**y2 mod m x**y3 mod m and x**y4 mod m
// Uses Montgomery representation.
func fourfoldExpNNMontgomery(x, m nat, y []*Int) []*Int {
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

	// powers[i] contains x^i
	var powers [2]nat
	powers[0] = powers[0].montgomery(one, RR, m, k0, numWords)
	powers[1] = powers[1].montgomery(x, RR, m, k0, numWords)

	// Zero round, find common bits of the four values
	//fmt.Println("test here, len = ", len([]nat{y[0].abs, y[1].abs, y[2].abs, y[3].abs}))
	yNew := fourfoldGcb([]nat{y[0].abs, y[1].abs, y[2].abs, y[3].abs})
	// First round, find common bits of the three values
	var cm012, cm013, cm023, cm123 nat
	cm012 = threefoldGcb(yNew[:3])
	cm013 = threefoldGcb([]nat{yNew[0], yNew[1], yNew[3]})
	cm023 = threefoldGcb([]nat{yNew[0], yNew[2], yNew[3]})
	cm123 = threefoldGcb(yNew[1:4])

	var cm01, cm23, cm02, cm13, cm03, cm12 nat
	yNew[0], yNew[1], cm01 = gcb(yNew[0], yNew[1])
	yNew[2], yNew[3], cm23 = gcb(yNew[2], yNew[3])
	yNew[0], yNew[2], cm02 = gcb(yNew[0], yNew[2])
	yNew[1], yNew[3], cm13 = gcb(yNew[1], yNew[3])
	yNew[0], yNew[3], cm03 = gcb(yNew[0], yNew[3])
	yNew[1], yNew[2], cm12 = gcb(yNew[1], yNew[2])
	//                                                                    0-4	  5     6      7       8     9     10     11    12    13    14
	z := multimontgomery(RR, m, powers[0], powers[1], k0, numWords, append(yNew, cm012, cm013, cm023, cm123, cm01, cm23, cm02, cm13, cm03, cm12))
	// calculate the actual values
	var temp nat
	temp = temp.make(numWords)
	// retrive common values for first number
	temp = temp.montgomery(z[0], z[4], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[0], z[5], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[0], z[6], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[0], z[7], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[0], z[9], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[0], z[11], m, k0, numWords)
	z[0], temp = temp, z[0]
	temp = temp.montgomery(z[0], z[13], m, k0, numWords)
	z[0], temp = temp, z[0]
	// retrive common values for second number
	temp = temp.montgomery(z[1], z[4], m, k0, numWords)
	z[1], temp = temp, z[1]
	temp = temp.montgomery(z[1], z[5], m, k0, numWords)
	z[1], temp = temp, z[1]
	temp = temp.montgomery(z[1], z[6], m, k0, numWords)
	z[1], temp = temp, z[1]
	temp = temp.montgomery(z[1], z[8], m, k0, numWords)
	z[1], temp = temp, z[1]
	temp = temp.montgomery(z[1], z[9], m, k0, numWords)
	z[1], temp = temp, z[1]
	temp = temp.montgomery(z[1], z[12], m, k0, numWords)
	z[1], temp = temp, z[1]
	temp = temp.montgomery(z[1], z[14], m, k0, numWords)
	z[1], temp = temp, z[1]
	// retrive common values for third number
	temp = temp.montgomery(z[2], z[4], m, k0, numWords)
	z[2], temp = temp, z[2]
	temp = temp.montgomery(z[2], z[5], m, k0, numWords)
	z[2], temp = temp, z[2]
	temp = temp.montgomery(z[2], z[7], m, k0, numWords)
	z[2], temp = temp, z[2]
	temp = temp.montgomery(z[2], z[8], m, k0, numWords)
	z[2], temp = temp, z[2]
	temp = temp.montgomery(z[2], z[10], m, k0, numWords)
	z[2], temp = temp, z[2]
	temp = temp.montgomery(z[2], z[11], m, k0, numWords)
	z[2], temp = temp, z[2]
	temp = temp.montgomery(z[2], z[14], m, k0, numWords)
	z[2], temp = temp, z[2]
	// retrive common values for four number
	temp = temp.montgomery(z[3], z[4], m, k0, numWords)
	z[3], temp = temp, z[3]
	temp = temp.montgomery(z[3], z[6], m, k0, numWords)
	z[3], temp = temp, z[3]
	temp = temp.montgomery(z[3], z[7], m, k0, numWords)
	z[3], temp = temp, z[3]
	temp = temp.montgomery(z[3], z[8], m, k0, numWords)
	z[3], temp = temp, z[3]
	temp = temp.montgomery(z[3], z[10], m, k0, numWords)
	z[3], temp = temp, z[3]
	temp = temp.montgomery(z[3], z[12], m, k0, numWords)
	z[3], temp = temp, z[3]
	temp = temp.montgomery(z[3], z[13], m, k0, numWords)
	z[3], temp = temp, z[3]

	z = z[:4] //the rest are useless now

	// convert to regular number
	for i := range z {
		temp = temp.montgomery(z[i], one, m, k0, numWords)
		z[i], temp = temp, z[i]
	}
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

	ret := make([]*Int, 4)
	for i := range ret {
		ret[i] = new(Int)
	}

	// normlize and set value
	for i := range z {
		z[i].norm()
		ret[i].abs = z[i]
		ret[i].neg = false
	}
	return ret
}
