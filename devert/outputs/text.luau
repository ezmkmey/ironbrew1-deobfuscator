local t = {
	"The quick brown fox jumps over the lazy dog. The dog sleeps; the fox runs on!",
	"Pack my box with five dozen liquor jugs, then pack the box again and again.",
	"How vexingly quick daft zebras jump: zebras jump, foxes run, dogs sleep soundly.",
	"Sphinx of black quartz, judge my vow; the vow is old and the quartz is black.",
	"Bright vixens jump; dozy fowl quack. The fowl sleep and the vixens run away.",
}

local t2 = { "lemon", "quartz", "abc", "zebra", "key" }

local function fn(s)
	local t3 = {}
	local t4 = {}
	local cnt = 0

	for s2 in string.gmatch(string.lower(s), "%a+") do
		cnt += 1

		if #s2 < 3 then
		else
			if t3[s2] == nil then
				t3[s2] = 0
				table.insert(t4, s2)
			end

			t3[s2] += 1
		end
	end

	table.sort(t4, function(a, b)
		if t3[a] == t3[b] then
			return a < b
		end
		return t3[a] > t3[b]
	end)

	return t3, t4, cnt
end

local function fn2(n, n2)
	if n >= 65 then
		if n <= 90 then
			return (n - 65 + n2) % 26 + 65
		end
	end

	if n >= 97 then
		if n <= 122 then
			return (n - 97 + n2) % 26 + 97
		end
	end

	return n
end

local function fn3(s, n)
	local buf = {}

	for i = 1, #s do
		buf[i] = string.char(fn2(string.byte(s, i), n))
	end

	return table.concat(buf)
end

local function fn4(s, s2, n)
	local buf = {}
	local cnt = 0
	local flag, byte

	for i = 1, #s do
		byte = string.byte(s, i)
		flag = byte >= 65

		if flag then
			flag = byte <= 90
		end

		if not flag then
			flag = byte >= 97

			if flag then
				flag = byte <= 122
			end
		end

		if flag then
			local len = #s2
			local n2 = string.byte(s2, cnt % len + 1) - 97
			local n3 = n * n2
			byte = fn2(byte, n3)
			cnt += 1
		end

		buf[i] = string.char(byte)
	end

	return table.concat(buf)
end

local function fn5(s)
	local buf = {}
	local pos = 1
	local pos2

	while pos <= #s do
		local ch = string.sub(s, pos, pos)
		pos2 = pos

		while true do
			local len = #s
			local more = pos2 < len and string.sub(s, pos2 + 1, pos2 + 1) == ch

			if more then
				pos2 += 1
			else
				break
			end
		end

		local n = pos2 - pos + 1

		if n > 1 then
			table.insert(buf, n .. ch)
		else
			table.insert(buf, ch)
		end

		pos = pos2 + 1
	end

	return table.concat(buf)
end

local function fn6(s)
	return (string.gsub(s, "(%d*)(%D)", function(v, s2)
		local n = tonumber(v) or 1
		return string.rep(s2, n)
	end))
end

local function fn7(s)
	local buf = {}
	local n, n2

	for i = 1, #s, 3 do
		local byte, byte2, byte3 = string.byte(s, i, i + 2)
		local n3 = byte * 65536
		local n4 = byte2 or 0
		local n5 = n3 + n4 * 256
		local n6 = byte3 or 0
		n = n5 + n6
		local buf2 = {}
		local n7 = -1
		n2 = 4 - n7

		while true do
			local n8 = n2 + n7
			n2 = n8

			if n8 >= 1 then
				local n9 = n % 64
				n = math.floor(n / 64)
				buf2[n8] = string.sub("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",
					n9 + 1, n9 + 1)
			else
				break
			end
		end

		if byte3 == nil then
			buf2[4] = "="

			if byte2 == nil then
				buf2[3] = "="
			end
		end

		table.insert(buf, table.concat(buf2))
	end

	return table.concat(buf)
end

local function fn8(s)
	local t3 = {}

	for i = 1, #"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" do
		t3[string.sub("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/",
			i, i)] = i - 1
	end

	local buf = {}
	local n, cnt, n2

	for i = 1, #s, 4 do
		n = 0
		cnt = 0

		for j = i, i + 3 do
			local char = string.sub(s, j, j)
			n2 = t3[char]

			if char == "=" then
				cnt += 1
				n2 = 0
			elseif n2 == nil then
				error({ position = j, char = char }, 0)
			end

			n = n * 64 + n2
		end

		local t4 = { math.floor(n / 65536), math.floor(n / 256) % 256, n % 256 }
		table.insert(buf, string.char(table.unpack(t4, 1, 3 - cnt)))
	end

	return table.concat(buf)
end

local function fn9(...)
	local cnt = select("#", ...)
	local t3 = { ... }

	return function(v)
		local v2 = v
		local buf = {}

		for i = 1, cnt do
			local v3 = t3[i](v2)
			v2 = v3
			buf[i] = #v3
		end

		return v2, table.concat(buf, ">")
	end
end

local function fn10(s, s2)
	local cnt = 0
	local pos = 1

	while true do
		local first, last = string.find(s, s2, pos, true)

		if first == nil then
			break
		else
			cnt += 1
			pos = last + 1
		end
	end

	return cnt
end

local function fn11(s, n)
	if #s <= n then
		return s
	end
	return string.sub(s, 1, n - 3) .. "..."
end

return function(n)
	local s = t[(n - 1) % #t + 1] .. " " .. t[n % #t + 1]
	local s2 = t2[n % #t2 + 1]
	local buf = {}
	local t3, t4, n2 = fn(s)
	local buf2 = {}

	for i = 1, math.min(6, #t4) do
		buf2[i] = string.format("%s:%d", t4[i], t3[t4[i]])
	end

	table.insert(buf,
		string.format("words %d, distinct long words %d, top %s", n2, #t4, table.concat(buf2, " ")))
	table.insert(buf, string.format("'the' occurs %d times, 'jump' %d times",
		fn10(string.lower(s), "the"), fn10(s, "jump")))
	local s3 = fn3(s, n * 3)
	table.insert(buf, "caesar " .. fn11(s3, 64))
	table.insert(buf, "caesar round trip " .. tostring(fn3(s3, -n * 3) == s))
	local s4 = fn4(s, s2, 1)
	table.insert(buf, "vigenere(" .. s2 .. ") " .. fn11(s4, 64))
	table.insert(buf, "vigenere round trip " .. tostring(fn4(s4, s2, -1) == s))
	local buf3 = {}

	for i = 1, math.min(5, #t4) do
		local s5 = t4[i]
		table.insert(buf3, string.rep(string.sub(s5, 1, 1), t3[s5] + (i + n) % 4))
	end

	local s6 = table.concat(buf3) .. string.rep("z", n)
	local s7 = fn5(s6)
	table.insert(buf, string.format("rle %s -> %s (%s)", s6, s7, tostring(fn6(s7) == s6)))
	local buf4 = {}

	for i = 1, 8 + n do
		buf4[i] = string.char((i * 37 + n * 11) % 256)
	end

	local s8 = table.concat(buf4)

	for _, s9 in ipairs({ string.sub(s, 1, n + 4), s8 }) do
		local s10 = fn7(s9)
		table.insert(buf,
			string.format("base64 %s (%d -> %d) %s", s10, #s9, #s10, tostring(fn8(s10) == s9)))
	end

	local ok, res = pcall(fn8, "QUJD*A==")
	table.insert(buf, if ok then "decoded bad base64"
		else string.format("bad base64 at %d: '%s'", res.position, res.char))
	local s11 = string.lower(t[n % #t + 1])

	local s12 = string.gsub(s11, "(%a)(%w*)", function(s5, s9)
		return string.upper(s5) .. s9
	end)

	local s13, v = (fn9(string.lower, function(s5)
		return (string.gsub(s5, "[^%a ]", ""))
	end, function(s5)
		return fn3(s5, n)
	end, fn7))(s12)

	table.insert(buf, "title " .. fn11(s12, 60))
	table.insert(buf, string.format("pipeline %s %s", v, fn11(s13, 48)))
	return table.concat(buf, "\n")
end
