local fns = {
	[2] = function(obj)
		obj.halted = true
		return 2
	end,
	[105] = function(obj)
		local n = obj:fetch()
		local p = obj.P
		local n2 = bit32.band(p, 1)
		local a = obj.A
		local n3 = a + n + n2
		local a2 = bit32.band(n3, 255)

		if not (n3 > 255) then
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		else
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		end

		local n4 = bit32.bxor(a, a2)
		local n5 = bit32.bxor(n, a2)
		local n6 = bit32.band(n4, n5)

		if bit32.band(n6, 128) ~= 0 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		end

		obj.A = a2
		obj:znupdate(a2)
		return 2
	end,
	[101] = function(obj)
		local n = obj:read((obj:fetch()))
		local p = obj.P
		local n2 = bit32.band(p, 1)
		local a = obj.A
		local n3 = a + n + n2
		local a2 = bit32.band(n3, 255)

		if n3 > 255 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		end

		local n4 = bit32.bxor(a, a2)
		local n5 = bit32.bxor(n, a2)
		local n6 = bit32.band(n4, n5)

		if bit32.band(n6, 128) ~= 0 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		end

		obj.A = a2
		obj:znupdate(a2)
		return 3
	end,
	[117] = function(obj)
		local n = obj:fetch() + obj.X
		local n2 = obj:read((bit32.band(n, 255)))
		local p = obj.P
		local n3 = bit32.band(p, 1)
		local a = obj.A
		local n4 = a + n2 + n3
		local a2 = bit32.band(n4, 255)

		if n4 > 255 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		end

		local n5 = bit32.bxor(a, a2)
		local n6 = bit32.bxor(n2, a2)
		local n7 = bit32.band(n5, n6)

		if bit32.band(n7, 128) ~= 0 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		end

		obj.A = a2
		obj:znupdate(a2)
		return 4
	end,
	[109] = function(obj)
		local n = obj:fetch()
		local n2 = obj:fetch()
		local n3 = obj:read(n + bit32.lshift(n2, 8))
		local p = obj.P
		local n4 = bit32.band(p, 1)
		local a = obj.A
		local n5 = a + n3 + n4
		local a2 = bit32.band(n5, 255)

		if n5 > 255 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		end

		local n6 = bit32.bxor(a, a2)
		local n7 = bit32.bxor(n3, a2)
		local n8 = bit32.band(n6, n7)

		if bit32.band(n8, 128) == 0 then
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		else
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		end

		obj.A = a2
		obj:znupdate(a2)
		return 4
	end,
	[125] = function(obj)
		local n = obj:fetch()
		local n2 = obj:fetch()
		local n3 = bit32.lshift(n2, 8) + n
		local n4 = n3 + obj.X
		local n5 = bit32.band(n4, 65535)
		local n6 = obj:read(n5)
		local p = obj.P
		local n7 = bit32.band(p, 1)
		local a = obj.A
		local n8 = a + n6 + n7
		local a2 = bit32.band(n8, 255)

		if n8 > 255 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		end

		local n9 = bit32.bxor(a, a2)
		local n10 = bit32.bxor(n6, a2)
		local n11 = bit32.band(n9, n10)

		if bit32.band(n11, 128) == 0 then
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		else
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		end

		obj.A = a2
		obj:znupdate(a2)
		local n12 = 4
		if bit32.band(n3, 65280) == bit32.band(n5, 65280) then
			return n12
		end
		return n12 + 1
	end,
	[121] = function(obj)
		local flag = false
		local t = { [true] = true, [false] = flag }
		local flag2 = false
		local n = obj:fetch()
		local n2 = obj:fetch()
		local n3 = n + bit32.lshift(n2, 8)
		local n4 = n3 + obj.Y
		local n5 = bit32.band(n4, 65535)
		local n6 = obj:read(n5)
		local p = obj.P
		local n7 = bit32.band(p, 1)
		local a = obj.A
		local n8 = a + n6 + n7
		local a2 = bit32.band(n8, 255)
		local flag3 = n8 > 255
		local t2 = { [t] = t, [true] = flag3, [false] = flag2 }
		t2[t] = t2
		t2[false] = flag2
		t2[true] = true

		if flag3 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		else
			t2[false] = flag2
			t2[true] = flag3
			t2[false] = flag2
			t2[true] = not flag2
			t[false] = flag
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		end

		local n9 = bit32.bxor(a, a2)
		local n10 = bit32.bxor(n6, a2)
		local n11 = bit32.band(n9, n10)

		if bit32.band(n11, 128) == 0 then
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		else
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		end

		obj.A = a2
		obj:znupdate(a2)
		local n12 = 4
		return if bit32.band(n3, 65280) == bit32.band(n5, 65280) then n12 else n12 + 1
	end,
	[97] = function(obj)
		local n = obj:fetch() + obj.X
		local n2 = bit32.band(n, 255)
		local n3 = obj:read(n2)
		local read = obj.read
		local n4 = n2 + 1
		local n5 = read(obj, (bit32.band(n4, 255)))
		local n6 = obj:read(n3 + bit32.lshift(n5, 8))
		local p = obj.P
		local n7 = bit32.band(p, 1)
		local a = obj.A
		local n8 = a + n6 + n7
		local a2 = bit32.band(n8, 255)

		if n8 > 255 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		end

		local n9 = bit32.bxor(a, a2)
		local n10 = bit32.bxor(n6, a2)
		local n11 = bit32.band(n9, n10)

		if bit32.band(n11, 128) == 0 then
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		else
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		end

		obj.A = a2
		obj:znupdate(a2)
		return 6
	end,
	[113] = function(obj)
		local flag = true
		local t = { [true] = flag, [false] = false }
		local flag2 = false
		local n = obj:fetch()
		local n2 = obj:read(n)
		local read = obj.read
		local n3 = n + 1
		local n4 = read(obj, (bit32.band(n3, 255)))
		local n5 = n2 + bit32.lshift(n4, 8)
		local n6 = n5 + obj.Y
		local n7 = bit32.band(n6, 65535)
		local n8 = obj:read(n7)
		local p = obj.P
		local n9 = bit32.band(p, 1)
		local a = obj.A
		local n10 = a + n8 + n9
		local a2 = bit32.band(n10, 255)
		local flag3 = n10 > 255
		local t2 = { [t] = t, [true] = flag3, [false] = flag2 }
		t2[t] = t2

		if not flag3 then
			t2[false] = flag2
			t2[true] = flag3
			t2[t] = t2
			t2[false] = flag2
			t2[true] = true
			t2[false] = flag2
			t2[true] = flag3
			t2[t] = t2
			t2[false] = flag2
			t2[true] = not flag2
			local flag4 = not flag2
			t2[false] = flag2
			t2[true] = flag3
			t2[false] = flag2
			t2[true] = flag4
			t2[false] = flag2
			t2[true] = flag4
			t[true] = flag
			local p2 = obj.P
			obj.P = bit32.band(p2, 254)
		else
			local p2 = obj.P
			obj.P = bit32.bor(p2, 1)
		end

		local n11 = bit32.bxor(a, a2)
		local n12 = bit32.bxor(n8, a2)
		local n13 = bit32.band(n11, n12)

		if bit32.band(n13, 128) ~= 0 then
			local p2 = obj.P
			obj.P = bit32.bor(p2, 64)
		else
			local p2 = obj.P
			obj.P = bit32.band(p2, 191)
		end

		obj.A = a2
		obj:znupdate(a2)
		local n14 = 5
		if bit32.band(n5, 65280) ~= bit32.band(n7, 65280) then
			return n14 + 1
		end
		return n14
	end,
	[41] = function(obj)
		local v = obj:fetch()
		local a = obj.A
		obj.A = bit32.band(a, v)
		obj.znupdate(obj, obj.A)
		return 2
	end,
}

fns[37] = function(obj)
	local v = obj:read((obj:fetch()))
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	return 3
end

fns[53] = function(obj)
	local n = obj:fetch() + obj.X
	local v = obj:read((bit32.band(n, 255)))
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	return 4
end

fns[45] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local v = obj:read(n + bit32.lshift(n2, 8))
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	return 4
end

fns[61] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	local v = obj:read(n5)
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	return if bit32.band(n3, 65280) == bit32.band(n5, 65280) then n6 else n6 + 1
end

fns[57] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	local v = obj:read(n5)
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	if bit32.band(n3, 65280) == bit32.band(n5, 65280) then
		return n6
	end
	return n6 + 1
end

fns[33] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	local v = obj:read(n3 + bit32.lshift(n5, 8))
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	return 6
end

fns[49] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = n + 1
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8)
	local n6 = n5 + obj.Y
	local n7 = bit32.band(n6, 65535)
	local v = obj:read(n7)
	local a = obj.A
	obj.A = bit32.band(a, v)
	obj.znupdate(obj, obj.A)
	local n8 = 5
	return if bit32.band(n5, 65280) == bit32.band(n7, 65280) then n8 else n8 + 1
end

fns[10] = function(obj)
	local a = obj.A
	local flag = (bit32.band(a, 128) ~= 0 and 1) or 0
	local a2 = obj.A
	local n = bit32.lshift(a2, 1)
	obj.A = bit32.band(n, 255)

	if flag == 1 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj.znupdate(obj, obj.A)
	return 2
end

fns[6] = function(obj)
	local v = obj:fetch()
	local n = obj:read(v)
	local flag = (bit32.band(n, 128) ~= 0 and 1) or 0
	local n2 = bit32.lshift(n, 1)
	local n3 = bit32.band(n2, 255)
	obj:write(v, n3)

	if flag == 1 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 5
end

fns[22] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local n4 = if bit32.band(n3, 128) ~= 0 then 1 else 0
	local n5 = bit32.lshift(n3, 1)
	local n6 = bit32.band(n5, 255)
	obj:write(n2, n6)

	if n4 == 1 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n6)
	return 6
end

fns[14] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3)
	local n5 = if bit32.band(n4, 128) ~= 0 then 1 else 0
	local n6 = bit32.lshift(n4, 1)
	local n7 = bit32.band(n6, 255)
	obj:write(n3, n7)

	if n5 == 1 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n7)
	return 6
end

fns[30] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	local n5 = obj:read(n4)
	local flag = (bit32.band(n5, 128) ~= 0 and 1) or 0
	local n6 = bit32.lshift(n5, 1)
	local n7 = bit32.band(n6, 255)
	obj:write(n4, n7)

	if flag == 1 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n7)
	return 7
end

fns[144] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 1) == 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if n3 ~= bit32.band(pc2, 65280) then
			cnt += 1
		end
	end

	return cnt
end

fns[176] = function(obj)
	local flag = true
	local t = { [true] = flag, [false] = false }
	local flag2 = false
	local t2 = { [t] = t }
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 1) ~= 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC
		local flag3 = n3 ~= bit32.band(pc2, 65280)
		t2[true] = flag3
		t2[false] = flag2
		t2[t] = t2
		t2[false] = flag2
		t2[true] = not flag2

		if not flag3 then
			t2[true] = flag3
			t2[false] = flag2
			t2[false] = flag2
			t2[true] = flag3
			t2[false] = flag2
			t2[true] = not flag2
			t[true] = flag
		else
			cnt += 1
		end
	end

	return cnt
end

fns[240] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 2) ~= 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if not (n3 == bit32.band(pc2, 65280)) then
			cnt += 1
		end
	end

	return cnt
end

fns[48] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 128) ~= 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if not (n3 == bit32.band(pc2, 65280)) then
			cnt += 1
		end
	end

	return cnt
end

fns[208] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 2) == 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if not (n3 == bit32.band(pc2, 65280)) then
			cnt += 1
		end
	end

	return cnt
end

fns[16] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 128) == 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if not (n3 == bit32.band(pc2, 65280)) then
			cnt += 1
		end
	end

	return cnt
end

fns[80] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if bit32.band(p, 64) == 0 then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if not (n3 == bit32.band(pc2, 65280)) then
			cnt += 1
		end
	end

	return cnt
end

fns[112] = function(obj)
	local n = obj:fetch()

	if n >= 128 then
		n -= 256
	end

	local cnt = 2
	local p = obj.P

	if not (bit32.band(p, 64) == 0) then
		local pc = obj.PC
		local n2 = obj.PC + n
		obj.PC = bit32.band(n2, 65535)
		cnt += 1
		local n3 = bit32.band(pc, 65280)
		local pc2 = obj.PC

		if not (n3 == bit32.band(pc2, 65280)) then
			cnt += 1
		end
	end

	return cnt
end

fns[36] = function(obj)
	local flag = false
	local t = { [true] = true, [false] = flag }
	local flag2 = false
	local t2 = { [t] = t }
	local n = obj:read((obj:fetch()))
	local a = obj.A

	if bit32.band(a, n) == 0 then
		local p = obj.P
		obj.P = bit32.bor(p, 2)
	else
		local p = obj.P
		obj.P = bit32.band(p, 253)
	end

	if bit32.band(n, 128) == 0 then
		local p = obj.P
		obj.P = bit32.band(p, 127)
	else
		local p = obj.P
		obj.P = bit32.bor(p, 128)
	end

	local flag3 = bit32.band(n, 64) ~= 0
	t2[false] = flag2
	t2[true] = flag3

	if flag3 then
		local p = obj.P
		obj.P = bit32.bor(p, 64)
	else
		t2[true] = flag3
		t2[false] = flag2
		t2[t] = t2
		t2[false] = flag2
		t2[true] = true
		t2[false] = flag2
		t2[true] = flag3
		t2[t] = t2
		t2[false] = flag2
		t2[true] = flag3
		t2[t] = t2
		t[false] = flag
		local p = obj.P
		obj.P = bit32.band(p, 191)
	end

	return 3
end

fns[44] = function(obj)
	local flag = true
	local t = { [true] = flag, [false] = false }
	local flag2 = false
	local t2 = { [t] = t }
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = obj:read(n + bit32.lshift(n2, 8))
	local a = obj.A

	if bit32.band(a, n3) == 0 then
		local p = obj.P
		obj.P = bit32.bor(p, 2)
	else
		local p = obj.P
		obj.P = bit32.band(p, 253)
	end

	local flag3 = bit32.band(n3, 128) ~= 0
	t2[true] = flag3
	t2[false] = flag2
	t2[false] = flag2
	t2[true] = not flag2

	if flag3 then
		local p = obj.P
		obj.P = bit32.bor(p, 128)
	else
		t2[true] = flag3
		t2[false] = flag2
		t2[t] = t2
		t2[false] = flag2
		t2[true] = not flag2
		t[true] = flag
		local p = obj.P
		obj.P = bit32.band(p, 127)
	end

	if bit32.band(n3, 64) ~= 0 then
		local p = obj.P
		obj.P = bit32.bor(p, 64)
	else
		local p = obj.P
		obj.P = bit32.band(p, 191)
	end

	return 4
end

fns[0] = function(obj)
	local n = obj.PC + 1
	obj.PC = bit32.band(n, 65535)
	local pc = obj.PC
	local push = obj.push
	local n2 = bit32.rshift(pc, 8)
	push(obj, (bit32.band(n2, 255)))
	obj.push(obj, (bit32.band(pc, 255)))
	local push2 = obj.push
	local p = obj.P
	push2(obj, (bit32.bor(p, 48)))
	local p2 = obj.P
	obj.P = bit32.bor(p2, 4)
	local mem = obj.memory
	local n3 = mem[65534]
	local n4 = mem[65535]
	obj.PC = n3 + bit32.lshift(n4, 8)
	return 7
end

fns[24] = function(obj)
	local p = obj.P
	obj.P = bit32.band(p, 254)
	return 2
end

fns[216] = function(obj)
	local p = obj.P
	obj.P = bit32.band(p, 247)
	return 2
end

fns[88] = function(obj)
	local p = obj.P
	obj.P = bit32.band(p, 251)
	return 2
end

fns[184] = function(obj)
	local p = obj.P
	obj.P = bit32.band(p, 191)
	return 2
end

fns[201] = function(obj)
	local n = obj:fetch()
	local n2 = obj.A - n
	local n3 = bit32.band(n2, 255)

	if n <= obj.A then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 2
end

fns[197] = function(obj)
	local n = obj:read((obj:fetch()))
	local n2 = obj.A - n
	local n3 = bit32.band(n2, 255)

	if not not (n <= obj.A) then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 3
end

fns[213] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = obj:read((bit32.band(n, 255)))
	local n3 = obj.A - n2
	local n4 = bit32.band(n3, 255)

	if n2 <= obj.A then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n4)
	return 4
end

fns[205] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = obj:read(n + bit32.lshift(n2, 8))
	local n4 = obj.A - n3
	local n5 = bit32.band(n4, 255)

	if n3 <= obj.A then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n5)
	return 4
end

fns[221] = function(obj)
	local flag = true
	local t = { [true] = flag, [false] = false }
	local flag2 = false
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	local n6 = obj:read(n5)
	local n7 = obj.A - n6
	local n8 = bit32.band(n7, 255)
	local flag3 = n6 <= obj.A
	local t2 = { [t] = t, [true] = flag3, [false] = flag2 }
	t2[t] = t2

	if not flag3 then
		t2[true] = flag3
		t2[false] = flag2
		t2[t] = t2
		t2[false] = flag2
		t2[true] = true
		t2[true] = flag3
		t2[false] = flag2
		t[true] = flag
		local p = obj.P
		obj.P = bit32.band(p, 254)
	else
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	end

	obj:znupdate(n8)
	local n9 = 4
	if bit32.band(n3, 65280) == bit32.band(n5, 65280) then
		return n9
	end
	return n9 + 1
end

fns[217] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	local n6 = obj:read(n5)
	local n7 = obj.A - n6
	local n8 = bit32.band(n7, 255)

	if not (n6 <= obj.A) then
		local p = obj.P
		obj.P = bit32.band(p, 254)
	else
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	end

	obj:znupdate(n8)
	local n9 = 4
	return if bit32.band(n3, 65280) == bit32.band(n5, 65280) then n9 else n9 + 1
end

fns[193] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	local n6 = obj:read(n3 + bit32.lshift(n5, 8))
	local n7 = obj.A - n6
	local n8 = bit32.band(n7, 255)

	if n6 <= obj.A then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n8)
	return 6
end

fns[209] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = n + 1
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8)
	local n6 = n5 + obj.Y
	local n7 = bit32.band(n6, 65535)
	local n8 = obj:read(n7)
	local n9 = obj.A - n8
	local n10 = bit32.band(n9, 255)

	if n8 <= obj.A then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n10)
	local n11 = 5
	if bit32.band(n5, 65280) ~= bit32.band(n7, 65280) then
		return n11 + 1
	end
	return n11
end

fns[224] = function(obj)
	local n = obj:fetch()
	local n2 = obj.X - n
	local n3 = bit32.band(n2, 255)

	if n <= obj.X then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 2
end

fns[228] = function(obj)
	local n = obj:read((obj:fetch()))
	local n2 = obj.X - n
	local n3 = bit32.band(n2, 255)

	if n <= obj.X then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 3
end

fns[236] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = obj:read(n + bit32.lshift(n2, 8))
	local n4 = obj.X - n3
	local n5 = bit32.band(n4, 255)

	if not not (n3 <= obj.X) then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n5)
	return 4
end

fns[192] = function(obj)
	local n = obj:fetch()
	local n2 = obj.Y - n
	local n3 = bit32.band(n2, 255)

	if n <= obj.Y then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 2
end

fns[196] = function(obj)
	local n = obj:read((obj:fetch()))
	local n2 = obj.Y - n
	local n3 = bit32.band(n2, 255)

	if n <= obj.Y then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n3)
	return 3
end

fns[204] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = obj:read(n + bit32.lshift(n2, 8))
	local n4 = obj.Y - n3
	local n5 = bit32.band(n4, 255)

	if n3 <= obj.Y then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n5)
	return 4
end

fns[198] = function(obj)
	local v = obj:fetch()
	local n = obj:read(v) - 1
	local n2 = bit32.band(n, 255)
	obj:write(v, n2)
	obj:znupdate(n2)
	return 5
end

fns[214] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2) - 1
	local n4 = bit32.band(n3, 255)
	obj:write(n2, n4)
	obj:znupdate(n4)
	return 6
end

fns[206] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3) - 1
	local n5 = bit32.band(n4, 255)
	obj:write(n3, n5)
	obj:znupdate(n5)
	return 6
end

fns[222] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	local n5 = obj:read(n4) - 1
	local n6 = bit32.band(n5, 255)
	obj:write(n4, n6)
	obj:znupdate(n6)
	return 7
end

fns[202] = function(obj)
	local n = obj.X - 1
	obj.X = bit32.band(n, 255)
	obj.znupdate(obj, obj.X)
	return 2
end

fns[136] = function(obj)
	local n = obj.Y - 1
	obj.Y = bit32.band(n, 255)
	obj.znupdate(obj, obj.Y)
	return 2
end

fns[73] = function(obj)
	local v = obj:fetch()
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	return 2
end

fns[69] = function(obj)
	local v = obj:read((obj:fetch()))
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	return 3
end

fns[85] = function(obj)
	local n = obj:fetch() + obj.X
	local v = obj:read((bit32.band(n, 255)))
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	return 4
end

fns[77] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local v = obj:read(n + bit32.lshift(n2, 8))
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	return 4
end

fns[93] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	local v = obj:read(n5)
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	return if bit32.band(n3, 65280) == bit32.band(n5, 65280) then n6 else n6 + 1
end

fns[89] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	local v = obj:read(n5)
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then
		return 1 + n6
	end
	return n6
end

fns[65] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	local v = obj:read(n3 + bit32.lshift(n5, 8))
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	return 6
end

fns[81] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = n + 1
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8)
	local n6 = n5 + obj.Y
	local n7 = bit32.band(n6, 65535)
	local v = obj:read(n7)
	local a = obj.A
	obj.A = bit32.bxor(a, v)
	obj.znupdate(obj, obj.A)
	local n8 = 5
	return if bit32.band(n5, 65280) ~= bit32.band(n7, 65280) then n8 + 1 else n8
end

fns[230] = function(obj)
	local v = obj:fetch()
	local n = obj:read(v) + 1
	local n2 = bit32.band(n, 255)
	obj:write(v, n2)
	obj:znupdate(n2)
	return 5
end

fns[246] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2) + 1
	local n4 = bit32.band(n3, 255)
	obj:write(n2, n4)
	obj:znupdate(n4)
	return 6
end

fns[238] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3) + 1
	local n5 = bit32.band(n4, 255)
	obj:write(n3, n5)
	obj:znupdate(n5)
	return 6
end

fns[254] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	local n5 = obj:read(n4) + 1
	local n6 = bit32.band(n5, 255)
	obj:write(n4, n6)
	obj:znupdate(n6)
	return 7
end

fns[232] = function(obj)
	local n = obj.X + 1
	obj.X = bit32.band(n, 255)
	obj.znupdate(obj, obj.X)
	return 2
end

fns[200] = function(obj)
	local n = obj.Y + 1
	obj.Y = bit32.band(n, 255)
	obj.znupdate(obj, obj.Y)
	return 2
end

fns[76] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	obj.PC = n + bit32.lshift(n2, 8)
	return 3
end

fns[108] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3)
	local n5 = if bit32.band(n3, 255) == 255
		then obj.read(obj, (bit32.band(n3, 65280))) else obj.read(obj, n3 + 1)
	obj.PC = n4 + bit32.lshift(n5, 8)
	return 5
end

fns[32] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local pc = n + bit32.lshift(n2, 8)
	local n3 = obj.PC - 1
	local n4 = bit32.band(n3, 65535)
	local push = obj.push
	local n5 = bit32.rshift(n4, 8)
	push(obj, (bit32.band(n5, 255)))
	obj.push(obj, (bit32.band(n4, 255)))
	obj.PC = pc
	return 6
end

fns[169] = function(obj)
	obj.A = obj:fetch()
	obj.znupdate(obj, obj.A)
	return 2
end

fns[165] = function(obj)
	obj.A = obj:read((obj:fetch()))
	obj.znupdate(obj, obj.A)
	return 3
end

fns[181] = function(obj)
	local n = obj:fetch() + obj.X
	obj.A = obj:read((bit32.band(n, 255)))
	obj.znupdate(obj, obj.A)
	return 4
end

fns[173] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	obj.A = obj:read(n + bit32.lshift(n2, 8))
	obj.znupdate(obj, obj.A)
	return 4
end

fns[189] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	obj.A = obj:read(n5)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	if bit32.band(n3, 65280) == bit32.band(n5, 65280) then
		return n6
	end
	return n6 + 1
end

fns[185] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	obj.A = obj:read(n5)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	return if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then n6 + 1 else n6
end

fns[161] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	obj.A = obj:read(n3 + bit32.lshift(n5, 8))
	obj.znupdate(obj, obj.A)
	return 6
end

fns[177] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = n + 1
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8)
	local n6 = n5 + obj.Y
	local n7 = bit32.band(n6, 65535)
	obj.A = obj:read(n7)
	obj.znupdate(obj, obj.A)
	local n8 = 5
	if bit32.band(n5, 65280) == bit32.band(n7, 65280) then
		return n8
	end
	return n8 + 1
end

fns[162] = function(obj)
	obj.X = obj:fetch()
	obj.znupdate(obj, obj.X)
	return 2
end

fns[166] = function(obj)
	obj.X = obj:read((obj:fetch()))
	obj.znupdate(obj, obj.X)
	return 3
end

fns[182] = function(obj)
	local n = obj:fetch() + obj.Y
	obj.X = obj:read((bit32.band(n, 255)))
	obj.znupdate(obj, obj.X)
	return 4
end

fns[174] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	obj.X = obj:read(n + bit32.lshift(n2, 8))
	obj.znupdate(obj, obj.X)
	return 4
end

fns[190] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	obj.X = obj:read(n5)
	obj.znupdate(obj, obj.X)
	local n6 = 4
	return if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then n6 + 1 else n6
end

fns[160] = function(obj)
	obj.Y = obj:fetch()
	obj.znupdate(obj, obj.Y)
	return 2
end

fns[164] = function(obj)
	obj.Y = obj:read((obj:fetch()))
	obj.znupdate(obj, obj.Y)
	return 3
end

fns[180] = function(obj)
	local n = obj:fetch() + obj.X
	obj.Y = obj:read((bit32.band(n, 255)))
	obj.znupdate(obj, obj.Y)
	return 4
end

fns[172] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	obj.Y = obj:read(n + bit32.lshift(n2, 8))
	obj.znupdate(obj, obj.Y)
	return 4
end

fns[188] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	obj.Y = obj:read(n5)
	obj.znupdate(obj, obj.Y)
	local n6 = 4
	if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then
		return n6 + 1
	end
	return n6
end

fns[74] = function(obj)
	local a = obj.A
	local n = bit32.band(a, 1)
	local a2 = obj.A
	local n2 = bit32.rshift(a2, 1)
	obj.A = bit32.band(n2, 255)

	if n == 0 then
		local p = obj.P
		obj.P = bit32.band(p, 254)
	else
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	end

	obj.znupdate(obj, obj.A)
	return 2
end

fns[70] = function(obj)
	local v = obj:fetch()
	local n = obj:read(v)
	local n2 = bit32.band(n, 1)
	local n3 = bit32.rshift(n, 1)
	local n4 = bit32.band(n3, 255)
	obj:write(v, n4)

	if n2 ~= 0 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n4)
	return 5
end

fns[86] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local n4 = bit32.band(n3, 1)
	local n5 = bit32.rshift(n3, 1)
	local n6 = bit32.band(n5, 255)
	obj:write(n2, n6)

	if n4 == 0 then
		local p = obj.P
		obj.P = bit32.band(p, 254)
	else
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	end

	obj:znupdate(n6)
	return 6
end

fns[78] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3)
	local n5 = bit32.band(n4, 1)
	local n6 = bit32.rshift(n4, 1)
	local n7 = bit32.band(n6, 255)
	obj:write(n3, n7)

	if n5 == 0 then
		local p = obj.P
		obj.P = bit32.band(p, 254)
	else
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	end

	obj:znupdate(n7)
	return 6
end

fns[94] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	local n5 = obj:read(n4)
	local n6 = bit32.band(n5, 1)
	local n7 = bit32.rshift(n5, 1)
	local n8 = bit32.band(n7, 255)
	obj:write(n4, n8)

	if n6 ~= 0 then
		local p = obj.P
		obj.P = bit32.bor(p, 1)
	else
		local p = obj.P
		obj.P = bit32.band(p, 254)
	end

	obj:znupdate(n8)
	return 7
end

fns[234] = function(obj)
	return 2
end

fns[9] = function(obj)
	local v = obj:fetch()
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	return 2
end

fns[5] = function(obj)
	local v = obj:read((obj:fetch()))
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	return 3
end

fns[21] = function(obj)
	local n = obj:fetch() + obj.X
	local v = obj:read((bit32.band(n, 255)))
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	return 4
end

fns[13] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local v = obj:read(n + bit32.lshift(n2, 8))
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	return 4
end

fns[29] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	local v = obj:read(n5)
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	return if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then n6 + 1 else n6
end

fns[25] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	local v = obj:read(n5)
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	local n6 = 4
	if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then
		return n6 + 1
	end
	return n6
end

fns[1] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	local v = obj:read(n3 + bit32.lshift(n5, 8))
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	return 6
end

fns[17] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = n + 1
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8)
	local n6 = n5 + obj.Y
	local n7 = bit32.band(n6, 65535)
	local v = obj:read(n7)
	local a = obj.A
	obj.A = bit32.bor(a, v)
	obj.znupdate(obj, obj.A)
	local n8 = 5
	return if bit32.band(n5, 65280) == bit32.band(n7, 65280) then n8 else n8 + 1
end

fns[72] = function(obj)
	obj.push(obj, obj.A)
	return 3
end

fns[8] = function(obj)
	local push = obj.push
	local p = obj.P
	push(obj, (bit32.bor(p, 16)))
	return 3
end

fns[104] = function(obj)
	obj.A = obj:pop()
	obj.znupdate(obj, obj.A)
	return 4
end

fns[40] = function(obj)
	local n = obj:pop()
	local n2 = bit32.band(n, 239)
	obj.P = bit32.bor(n2, 32)
	return 4
end

fns[42] = function(obj)
	local p = obj.P
	local n = bit32.band(p, 1)
	local a = obj.A
	local flag = (bit32.band(a, 128) ~= 0 and 1) or 0
	local a2 = obj.A
	local n2 = bit32.lshift(a2, 1)
	local n3 = bit32.band(n2, 255)
	obj.A = bit32.bor(n3, n)

	if flag == 1 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj.znupdate(obj, obj.A)
	return 2
end

fns[38] = function(obj)
	local v = obj:fetch()
	local n = obj:read(v)
	local p = obj.P
	local n2 = bit32.band(p, 1)
	local n3 = if bit32.band(n, 128) ~= 0 then 1 else 0
	local n4 = bit32.lshift(n, 1)
	local n5 = bit32.band(n4, 255)
	local n6 = bit32.bor(n5, n2)
	obj:write(v, n6)

	if n3 == 1 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj:znupdate(n6)
	return 5
end

fns[54] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local p = obj.P
	local n4 = bit32.band(p, 1)
	local n5 = if bit32.band(n3, 128) ~= 0 then 1 else 0
	local n6 = bit32.lshift(n3, 1)
	local n7 = bit32.band(n6, 255)
	local n8 = bit32.bor(n7, n4)
	obj:write(n2, n8)

	if n5 == 1 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj:znupdate(n8)
	return 6
end

fns[46] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3)
	local p = obj.P
	local n5 = bit32.band(p, 1)
	local flag = (bit32.band(n4, 128) ~= 0 and 1) or 0
	local n6 = bit32.lshift(n4, 1)
	local n7 = bit32.band(n6, 255)
	local n8 = bit32.bor(n7, n5)
	obj:write(n3, n8)

	if flag == 1 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj:znupdate(n8)
	return 6
end

fns[62] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	local n5 = obj:read(n4)
	local p = obj.P
	local n6 = bit32.band(p, 1)
	local n7 = if bit32.band(n5, 128) ~= 0 then 1 else 0
	local n8 = bit32.lshift(n5, 1)
	local n9 = bit32.band(n8, 255)
	local n10 = bit32.bor(n9, n6)
	obj:write(n4, n10)

	if n7 == 1 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj:znupdate(n10)
	return 7
end

fns[106] = function(obj)
	local p = obj.P
	local n = bit32.band(p, 1)
	local n2 = bit32.lshift(n, 7)
	local a = obj.A
	local n3 = bit32.band(a, 1)
	local a2 = obj.A
	local n4 = bit32.rshift(a2, 1)
	obj.A = bit32.bor(n4, n2)

	if n3 ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj.znupdate(obj, obj.A)
	return 2
end

fns[102] = function(obj)
	local v = obj:fetch()
	local n = obj:read(v)
	local p = obj.P
	local n2 = bit32.band(p, 1)
	local n3 = bit32.lshift(n2, 7)
	local n4 = bit32.band(n, 1)
	local n5 = bit32.rshift(n, 1)
	local n6 = bit32.bor(n5, n3)
	obj:write(v, n6)

	if n4 == 0 then
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	else
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	end

	obj:znupdate(n6)
	return 5
end

fns[118] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local p = obj.P
	local n4 = bit32.band(p, 1)
	local n5 = bit32.lshift(n4, 7)
	local n6 = bit32.band(n3, 1)
	local n7 = bit32.rshift(n3, 1)
	local n8 = bit32.bor(n7, n5)
	obj:write(n2, n8)

	if n6 == 0 then
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	else
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	end

	obj:znupdate(n8)
	return 6
end

fns[110] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = obj:read(n3)
	local p = obj.P
	local n5 = bit32.band(p, 1)
	local n6 = bit32.lshift(n5, 7)
	local n7 = bit32.band(n4, 1)
	local n8 = bit32.rshift(n4, 1)
	local n9 = bit32.bor(n8, n6)
	obj:write(n3, n9)

	if n7 ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj:znupdate(n9)
	return 6
end

fns[126] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	local n5 = obj:read(n4)
	local p = obj.P
	local n6 = bit32.band(p, 1)
	local n7 = bit32.lshift(n6, 7)
	local n8 = bit32.band(n5, 1)
	local n9 = bit32.rshift(n5, 1)
	local n10 = bit32.bor(n9, n7)
	obj:write(n4, n10)

	if n8 ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	obj:znupdate(n10)
	return 7
end

fns[64] = function(obj)
	local n = obj:pop()
	local n2 = bit32.band(n, 239)
	obj.P = bit32.bor(n2, 32)
	local n3 = obj:pop()
	local n4 = obj:pop()
	obj.PC = n3 + bit32.lshift(n4, 8)
	return 6
end

fns[96] = function(obj)
	local n = obj:pop()
	local n2 = obj:pop()
	local n3 = n + bit32.lshift(n2, 8) + 1
	obj.PC = bit32.band(n3, 65535)
	return 6
end

fns[233] = function(obj)
	local n = obj:fetch()
	local p = obj.P
	local n2 = bit32.band(p, 1)
	local a = obj.A
	local n3 = a - n - (1 - n2)
	local a2 = bit32.band(n3, 255)

	if n3 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n4 = bit32.bxor(a, a2)
	local n5 = bit32.bxor(a, n)
	local n6 = bit32.band(n4, n5)

	if bit32.band(n6, 128) == 0 then
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	else
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	end

	obj.A = a2
	obj:znupdate(a2)
	return 2
end

fns[229] = function(obj)
	local n = obj:read((obj:fetch()))
	local p = obj.P
	local n2 = bit32.band(p, 1)
	local a = obj.A
	local n3 = a - n - (1 - n2)
	local a2 = bit32.band(n3, 255)

	if n3 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n4 = bit32.bxor(a, a2)
	local n5 = bit32.bxor(a, n)
	local n6 = bit32.band(n4, n5)

	if bit32.band(n6, 128) ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	end

	obj.A = a2
	obj:znupdate(a2)
	return 3
end

fns[245] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = obj:read((bit32.band(n, 255)))
	local p = obj.P
	local n3 = bit32.band(p, 1)
	local a = obj.A
	local n4 = a - n2 - (1 - n3)
	local a2 = bit32.band(n4, 255)

	if n4 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n5 = bit32.bxor(a, a2)
	local n6 = bit32.bxor(a, n2)
	local n7 = bit32.band(n5, n6)

	if bit32.band(n7, 128) ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	end

	obj.A = a2
	obj:znupdate(a2)
	return 4
end

fns[237] = function(obj)
	local flag = false
	local t = { [true] = true, [false] = flag }
	local flag2 = false
	local t2 = { [t] = t }
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = obj:read(n + bit32.lshift(n2, 8))
	local p = obj.P
	local n4 = bit32.band(p, 1)
	local a = obj.A
	local n5 = a - n3 - (1 - n4)
	local a2 = bit32.band(n5, 255)

	if n5 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n6 = bit32.bxor(a, a2)
	local n7 = bit32.bxor(a, n3)
	local n8 = bit32.band(n6, n7)
	local flag3 = bit32.band(n8, 128) ~= 0
	t2[false] = flag2
	t2[true] = flag3
	t2[false] = flag2
	t2[true] = not flag2

	if not flag3 then
		t2[false] = flag2
		t2[true] = flag3
		t2[t] = t2
		t2[false] = flag2
		t2[true] = true
		t2[false] = flag2
		t2[true] = flag3
		t2[t] = t2
		t2[false] = flag2
		t2[true] = not flag2
		t[false] = flag
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	else
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	end

	obj.A = a2
	obj:znupdate(a2)
	return 4
end

fns[253] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.X
	local n5 = bit32.band(n4, 65535)
	local n6 = obj:read(n5)
	local p = obj.P
	local n7 = bit32.band(p, 1)
	local a = obj.A
	local n8 = a - n6 - (1 - n7)
	local a2 = bit32.band(n8, 255)

	if n8 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n9 = bit32.bxor(a, a2)
	local n10 = bit32.bxor(a, n6)
	local n11 = bit32.band(n9, n10)

	if not (bit32.band(n11, 128) ~= 0) then
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	else
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	end

	obj.A = a2
	obj:znupdate(a2)
	local n12 = 4
	if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then
		return n12 + 1
	end
	return n12
end

fns[249] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	local n4 = n3 + obj.Y
	local n5 = bit32.band(n4, 65535)
	local n6 = obj:read(n5)
	local p = obj.P
	local n7 = bit32.band(p, 1)
	local a = obj.A
	local n8 = a - n6 - (1 - n7)
	local a2 = bit32.band(n8, 255)

	if n8 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n9 = bit32.bxor(a, a2)
	local n10 = bit32.bxor(a, n6)
	local n11 = bit32.band(n9, n10)

	if bit32.band(n11, 128) == 0 then
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	else
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	end

	obj.A = a2
	obj:znupdate(a2)
	local n12 = 4
	return if bit32.band(n3, 65280) ~= bit32.band(n5, 65280) then n12 + 1 else n12
end

fns[225] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	local n6 = obj:read(n3 + bit32.lshift(n5, 8))
	local p = obj.P
	local n7 = bit32.band(p, 1)
	local a = obj.A
	local n8 = a - n6 - (1 - n7)
	local a2 = bit32.band(n8, 255)

	if n8 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n9 = bit32.bxor(a, a2)
	local n10 = bit32.bxor(a, n6)
	local n11 = bit32.band(n9, n10)

	if bit32.band(n11, 128) ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	end

	obj.A = a2
	obj:znupdate(a2)
	return 6
end

fns[241] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = n + 1
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8)
	local n6 = n5 + obj.Y
	local n7 = bit32.band(n6, 65535)
	local n8 = obj:read(n7)
	local p = obj.P
	local n9 = bit32.band(p, 1)
	local a = obj.A
	local n10 = a - n8 - (1 - n9)
	local a2 = bit32.band(n10, 255)

	if n10 >= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 1)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 254)
	end

	local n11 = bit32.bxor(a, a2)
	local n12 = bit32.bxor(a, n8)
	local n13 = bit32.band(n11, n12)

	if bit32.band(n13, 128) ~= 0 then
		local p2 = obj.P
		obj.P = bit32.bor(p2, 64)
	else
		local p2 = obj.P
		obj.P = bit32.band(p2, 191)
	end

	obj.A = a2
	obj:znupdate(a2)
	local n14 = 5
	if bit32.band(n5, 65280) == bit32.band(n7, 65280) then
		return n14
	end
	return n14 + 1
end

fns[56] = function(obj)
	local p = obj.P
	obj.P = bit32.bor(p, 1)
	return 2
end

fns[248] = function(obj)
	local p = obj.P
	obj.P = bit32.bor(p, 8)
	return 2
end

fns[120] = function(obj)
	local p = obj.P
	obj.P = bit32.bor(p, 4)
	return 2
end

fns[133] = function(obj)
	local v = obj:fetch()
	obj.write(obj, v, obj.A)
	return 3
end

fns[149] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	obj.write(obj, n2, obj.A)
	return 4
end

fns[141] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	obj.write(obj, n3, obj.A)
	return 4
end

fns[157] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.X
	local n4 = bit32.band(n3, 65535)
	obj.write(obj, n4, obj.A)
	return 5
end

fns[153] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8) + obj.Y
	local n4 = bit32.band(n3, 65535)
	obj.write(obj, n4, obj.A)
	return 5
end

fns[129] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	local n3 = obj:read(n2)
	local read = obj.read
	local n4 = n2 + 1
	local n5 = read(obj, (bit32.band(n4, 255)))
	local n6 = n3 + bit32.lshift(n5, 8)
	obj.write(obj, n6, obj.A)
	return 6
end

fns[145] = function(obj)
	local n = obj:fetch()
	local n2 = obj:read(n)
	local read = obj.read
	local n3 = 1 + n
	local n4 = read(obj, (bit32.band(n3, 255)))
	local n5 = n2 + bit32.lshift(n4, 8) + obj.Y
	local n6 = bit32.band(n5, 65535)
	obj.write(obj, n6, obj.A)
	return 6
end

fns[134] = function(obj)
	local v = obj:fetch()
	obj.write(obj, v, obj.X)
	return 3
end

fns[150] = function(obj)
	local n = obj:fetch() + obj.Y
	local n2 = bit32.band(n, 255)
	obj.write(obj, n2, obj.X)
	return 4
end

fns[142] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	obj.write(obj, n3, obj.X)
	return 4
end

fns[132] = function(obj)
	local v = obj:fetch()
	obj.write(obj, v, obj.Y)
	return 3
end

fns[148] = function(obj)
	local n = obj:fetch() + obj.X
	local n2 = bit32.band(n, 255)
	obj.write(obj, n2, obj.Y)
	return 4
end

fns[140] = function(obj)
	local n = obj:fetch()
	local n2 = obj:fetch()
	local n3 = n + bit32.lshift(n2, 8)
	obj.write(obj, n3, obj.Y)
	return 4
end

local cls = {}
cls.__index = cls

cls.new = function()
	local self = setmetatable({}, cls)
	self.A = 0
	self.X = 0
	self.Y = 0
	self.SP = 253
	self.PC = 0
	self.P = 36
	self.cycles = 0
	self.halted = false
	self.memory = {}

	for i = 0, 65535 do
		self.memory[i] = 0
	end

	return self
end

cls.read = function(self, v)
	return self.memory[v]
end

cls.write = function(self, v, n)
	self.memory[v] = bit32.band(n, 255)
end

cls.fetch = function(self)
	local pc = self.PC
	local v = self.memory[pc]
	local n = pc + 1
	self.PC = bit32.band(n, 65535)
	return v
end

cls.znupdate = function(self, n)
	if n == 0 then
		local p = self.P
		self.P = bit32.bor(p, 2)
	else
		local p = self.P
		self.P = bit32.band(p, 253)
	end

	if bit32.band(n, 128) ~= 0 then
		local p = self.P
		self.P = bit32.bor(p, 128)
	else
		local p = self.P
		self.P = bit32.band(p, 127)
	end
end

cls.step = function(self)
	local v = self:fetch()
	local fn = fns[v]
	if fn then
		self.cycles = self.cycles + fn(self)
		return
	end
	error(string.format("opcode 0x%02X not implemented.", v))
end

cls.push = function(self, v)
	local sp = self.SP
	self.write(self, 256 + sp, v)
	local n = sp - 1
	self.SP = bit32.band(n, 255)
end

cls.pop = function(self)
	local n = self.SP + 1
	self.SP = bit32.band(n, 255)
	return self.read(self, 256 + self.SP)
end

cls.reset = function(self)
	local mem = self.memory
	local n = mem[65532]
	local n2 = mem[65533]
	self.PC = n + bit32.lshift(n2, 8)
	self.SP = 253
	self.P = 36
	self.halted = false
end

cls.irq = function(self)
	local p = self.P

	if bit32.band(p, 4) == 0 then
		local pc = self.PC
		local push = self.push
		local n = bit32.rshift(pc, 8)
		push(self, (bit32.band(n, 255)))
		self.push(self, (bit32.band(pc, 255)))
		local push2 = self.push
		local n2 = bit32.band(p, 239)
		push2(self, (bit32.bor(n2, 32)))
		self.P = bit32.bor(p, 4)
		local mem = self.memory
		local n3 = mem[65534]
		local n4 = mem[65535]
		self.PC = n3 + bit32.lshift(n4, 8)
		self.cycles += 7
	end
end

cls.nmi = function(self)
	local p = self.P
	local pc = self.PC
	local push = self.push
	local n = bit32.rshift(pc, 8)
	push(self, (bit32.band(n, 255)))
	self.push(self, (bit32.band(pc, 255)))
	local push2 = self.push
	local n2 = bit32.band(p, 239)
	push2(self, (bit32.bor(n2, 32)))
	self.P = bit32.bor(p, 4)
	local mem = self.memory
	local n3 = mem[65530]
	local n4 = mem[65531]
	self.PC = n3 + bit32.lshift(n4, 8)
	self.cycles += 8
end

local obj = cls.new()

io = {
	buffer = "",
	write = function(s)
		io.buffer = io.buffer .. s
	end,
	flush = function()
		print(io.buffer)
		io.buffer = ""
	end,
}

obj.write = function(self, v, n)
	if v == 65280 then
		io.write(string.char(n))
	else
		self.memory[v] = bit32.band(n, 255)
	end
end

local n = 32768

local t = {
	169,
	99,
	141,
	0,
	2,
	169,
	1,
	141,
	1,
	2,
	169,
	113,
	141,
	2,
	2,
	169,
	0,
	141,
	3,
	2,
	173,
	0,
	2,
	24,
	233,
	113,
	141,
	0,
	2,
	173,
	1,
	2,
	233,
	0,
	141,
	1,
	2,
	169,
	1,
	24,
	109,
	3,
	2,
	141,
	3,
	2,
	173,
	0,
	2,
	24,
	233,
	113,
	141,
	0,
	2,
	173,
	1,
	2,
	24,
	233,
	0,
	141,
	1,
	2,
	173,
	3,
	2,
	24,
	105,
	1,
	141,
	3,
	2,
	173,
	0,
	2,
	24,
	233,
	113,
	141,
	0,
	2,
	173,
	1,
	2,
	24,
	233,
	0,
	141,
	1,
	2,
	173,
	3,
	2,
	24,
	105,
	1,
	141,
	3,
	2,
	173,
	0,
	2,
	141,
	4,
	2,
	173,
	3,
	2,
	105,
	48,
	141,
	0,
	255,
	169,
	46,
	141,
	0,
	255,
	169,
	64,
	141,
	5,
	2,
	169,
	6,
	141,
	6,
	2,
	169,
	0,
	141,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	5,
	2,
	24,
	233,
	113,
	141,
	5,
	2,
	173,
	6,
	2,
	24,
	233,
	0,
	141,
	6,
	2,
	238,
	7,
	2,
	173,
	7,
	2,
	56,
	233,
	10,
	141,
	9,
	2,
	24,
	169,
	1,
	141,
	8,
	2,
	173,
	8,
	2,
	24,
	105,
	48,
	141,
	0,
	255,
	173,
	9,
	2,
	24,
	105,
	48,
	141,
	0,
	255,
	76,
	199,
	128,
}

for i = 1, #t do
	obj.memory[n + i - 1] = t[i]
end

obj.memory[65532] = bit32.band(n, 255)
local mem = obj.memory
local n2 = bit32.rshift(n, 8)
mem[65533] = bit32.band(n2, 255)
obj:reset()

while not obj.halted do
	obj:step()
end

io.flush()
local obj2 = cls.new()
local fontfac, overlay
local t2 = {}
local s = ""

local t3 = { [53264] = function(n3)
	s = s .. string.char(n3)
end }

local t4 = { prefix = "Output: " }

t4.getter = function()
	return s
end

t4.y = 10

local t5 = {
	prefix = "Cycles: ",
	getter = function()
		return obj2.cycles
	end,
	y = 30,
}

local t6 = {
	prefix = "Accumulator (A): ",
	getter = function()
		return obj2.A
	end,
	y = 60,
}

local t7 = {
	prefix = "X Register: ",
	getter = function()
		return obj2.X
	end,
	y = 80,
}

local t8 = {
	prefix = "Y Register: ",
	getter = function()
		return obj2.Y
	end,
}

t8.y = 100

local t9 = {
	prefix = "Stack Pointer (SP): ",
	getter = function()
		return obj2.SP
	end,
	y = 120,
}

local t10 = {
	prefix = "Program Counter (PC): ",
	getter = function()
		return obj2.PC
	end,
}

t10.y = 140

local t11 = {
	prefix = "Processor Status (P): ",
	getter = function()
		return obj2.P
	end,
	y = 160,
}

local t12 = {
	prefix = "Halted: ",
	getter = function()
		return tostring(obj2.halted)
	end,
}

t12.y = 180

local t13 = {
	t4,
	t5,
	t6,
	t7,
	t8,
	t9,
	t10,
	t11,
	t12,
}

obj2.write = function(self, v, n3)
	self.memory[v] = bit32.band(n3, 255)

	if t3[v] then
		t3[v](n3)
	end
end

local n3 = 32768
local n4 = 1
obj2.memory[n3 + 1 - n4] = 169
obj2.memory[n3 + 2 - n4] = 72
obj2.memory[n3 + 3 - n4] = 141
obj2.memory[n3 + 4 - n4] = 16
obj2.memory[n3 + 5 - n4] = 208
obj2.memory[n3 + 6 - n4] = 169
obj2.memory[n3 + 7 - n4] = 101
obj2.memory[n3 + 8 - n4] = 141
obj2.memory[n3 + 9 - n4] = 16
obj2.memory[n3 + 10 - n4] = 208
obj2.memory[n3 + 11 - n4] = 169
obj2.memory[n3 + 12 - n4] = 108
obj2.memory[n3 + 13 - n4] = 141
obj2.memory[n3 + 14 - n4] = 16
obj2.memory[n3 + 15 - n4] = 208
obj2.memory[n3 + 16 - n4] = 169
obj2.memory[n3 + 17 - n4] = 108
obj2.memory[n3 + 18 - n4] = 141
obj2.memory[n3 + 19 - n4] = 16
obj2.memory[n3 + 20 - n4] = 208
obj2.memory[n3 + 21 - n4] = 169
obj2.memory[n3 + 22 - n4] = 111
obj2.memory[n3 + 23 - n4] = 141
obj2.memory[n3 + 24 - n4] = 16
obj2.memory[n3 + 25 - n4] = 208
obj2.memory[n3 + 26 - n4] = 169
obj2.memory[n3 + 27 - n4] = 32
obj2.memory[n3 + 28 - n4] = 141
obj2.memory[n3 + 29 - n4] = 16
obj2.memory[n3 + 30 - n4] = 208
obj2.memory[n3 + 31 - n4] = 169
obj2.memory[n3 + 32 - n4] = 102
obj2.memory[n3 + 33 - n4] = 141
obj2.memory[n3 + 34 - n4] = 16
obj2.memory[n3 + 35 - n4] = 208
obj2.memory[n3 + 36 - n4] = 169
obj2.memory[n3 + 37 - n4] = 114
obj2.memory[n3 + 38 - n4] = 141
obj2.memory[n3 + 39 - n4] = 16
obj2.memory[n3 + 40 - n4] = 208
obj2.memory[n3 + 41 - n4] = 169
obj2.memory[n3 + 42 - n4] = 111
obj2.memory[n3 + 43 - n4] = 141
obj2.memory[n3 + 44 - n4] = 16
obj2.memory[n3 + 45 - n4] = 208
obj2.memory[n3 + 46 - n4] = 169
obj2.memory[n3 + 47 - n4] = 109
obj2.memory[n3 + 48 - n4] = 141
obj2.memory[n3 + 49 - n4] = 16
obj2.memory[n3 + 50 - n4] = 208
obj2.memory[n3 + 51 - n4] = 169
obj2.memory[n3 + 52 - n4] = 32
obj2.memory[n3 + 53 - n4] = 141
obj2.memory[n3 + 54 - n4] = 16
obj2.memory[n3 + 55 - n4] = 208
obj2.memory[n3 + 56 - n4] = 169
obj2.memory[n3 + 57 - n4] = 54
obj2.memory[n3 + 58 - n4] = 141
obj2.memory[n3 + 59 - n4] = 16
obj2.memory[n3 + 60 - n4] = 208
obj2.memory[n3 + 61 - n4] = 169
obj2.memory[n3 + 62 - n4] = 53
obj2.memory[n3 + 63 - n4] = 141
obj2.memory[n3 + 64 - n4] = 16
obj2.memory[n3 + 65 - n4] = 208
obj2.memory[n3 + 66 - n4] = 169
obj2.memory[n3 + 67 - n4] = 48
obj2.memory[n3 + 68 - n4] = 141
obj2.memory[n3 + 69 - n4] = 16
obj2.memory[n3 + 70 - n4] = 208
obj2.memory[n3 + 71 - n4] = 169
obj2.memory[n3 + 72 - n4] = 50
obj2.memory[n3 + 73 - n4] = 141
obj2.memory[n3 + 74 - n4] = 16
obj2.memory[n3 + 75 - n4] = 208
obj2.memory[n3 + 76 - n4] = 169
obj2.memory[n3 + 77 - n4] = 33
obj2.memory[n3 + 78 - n4] = 141
obj2.memory[n3 + 79 - n4] = 16
obj2.memory[n3 + 80 - n4] = 208
obj2.memory[n3 + 81 - n4] = 2
obj2.memory[65532] = bit32.band(n3, 255)
local mem2 = obj2.memory
local n5 = bit32.rshift(n3, 8)
mem2[65533] = bit32.band(n5, 255)

setup = function()
	_G.engine = (((((((EngineFactory.new()):with_title("MOS6502")):with_width(1920)):with_height(1080)):with_scale(3)):with_gravity(9.8)):with_fullscreen(false)):create()
	overlay = engine:overlay()
	fontfac = engine:fontfactory()
	local font = fontfac:get("fixedsys")

	for i, t14 in ipairs(t13) do
		local obj3 = overlay
		local widget = obj3.create(obj3, WidgetType.label)
		widget.font = font
		widget.set(widget, t14.prefix .. "0", 10, t14.y)
		t2[i] = { widget = widget, prefix = t14.prefix, getter = t14.getter, y = t14.y }
	end

	obj2:reset()
end

loop = function()
	if obj2.halted then
		obj2:reset()
		s = ""
	else
		obj2:step()
	end

	for i = 1, #t2 do
		local t14 = t2[i]
		local widget = t14.widget
		widget.set(widget, t14.prefix .. t14.getter(), 10, t14.y)
	end
end

run = function()
	engine:run()
end
