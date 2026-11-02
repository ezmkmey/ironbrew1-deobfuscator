local t = { "push", "load", "store", "binary", "neg", "jump", "jumpf", "out", "halt" }

local t2 = {
	["+"] = function(n, n2)
		return n + n2
	end,
	["-"] = function(n, n2)
		return n - n2
	end,
	["*"] = function(n, n2)
		return n * n2
	end,
	["/"] = function(n, n2)
		if n2 == 0 then
			error("division by zero", 0)
		end

		return math.floor(n / n2)
	end,
	["%"] = function(n, n2)
		return n % n2
	end,
	["<"] = function(n, n2)
		if n < n2 then
			local n3 = 1
			return n3
		end
		return 0
	end,
	[">"] = function(n, n2)
		local n3

		if n2 < n then
			local n4 = 1
			n3 = n4
		else
			n3 = 0
		end

		return n3
	end,
	["=="] = function(v, v2)
		if v == v2 then
			local n = 1
			return n
		end
		return 0
	end,
}

local t3 = { { "==", "<", ">" }, { "+", "-" }, { "*", "/", "%" } }

local function fn(s)
	local toks = {}
	local line = 1
	local pos = 1
	local n, n2

	while pos <= #s do
		local ch = string.sub(s, pos, pos)
		local first, last = string.find(s, "^%d+", pos)
		n2 = last

		if ch == "\n" then
			line += 1
			n2 = pos
		elseif (ch == " " or ch == "\t") then
			n2 = pos
		elseif first == nil then
			local first2, last2 = string.find(s, "^%a%w*", pos)
			n = first2
			n2 = last2

			if first2 == nil then
				local first3, last3 = string.find(s, "^==", pos)
				n = first3
				n2 = last3

				if first3 == nil then
					n = pos
					n2 = pos
				end
			end

			table.insert(toks, { kind = "word", text = string.sub(s, n, n2), line = line })
		else
			table.insert(toks,
				{ kind = "number", text = tonumber(string.sub(s, first, n2)), line = line })
		end

		pos = n2 + 1
	end

	table.insert(toks, { kind = "end", text = "<end>", line = line })
	return toks
end

local function fn2(s, t4)
	local toks = fn(s)
	local idx = 1
	local t5 = {}
	local t6 = {}
	local cnt = 0

	local function emit(n, v)
		table.insert(t5, { n, v })
		return #t5
	end

	local function fail(msg)
		error({ kind = "syntax", line = toks[idx].line, message = msg }, 0)
	end

	local function fn3(v)
		if toks[idx].text == v then
			idx += 1
			return true
		end
		return false
	end

	local function fn4(s2)
		if not fn3(s2) then
			fail("expected '" .. s2 .. "' near '" .. tostring(toks[idx].text) .. "'")
		end
	end

	local function fn5(s2, flag)
		if t6[s2] == nil then
			if not flag then
				fail("undeclared variable '" .. s2 .. "'")
			end

			cnt += 1
			t6[s2] = cnt
		end

		return t6[s2]
	end

	local fn6

	local function fn7()
		local tok = toks[idx]
		idx += 1

		if tok.kind == "number" then
			emit(1, tok.text)
		elseif tok.text == "(" then
			fn6(1)
			fn4(")")
		elseif tok.text == "-" then
			fn7()
			emit(5)
		else
			local flag = tok.kind == "word"

			if not (not flag) then
				flag = string.find(tok.text, "^%a")
			end

			if flag then
				local emit2 = emit
				emit2(2, fn5(tok.text, false))
			else
				idx -= 1
				fail("unexpected '" .. tostring(tok.text) .. "'")
			end
		end
	end

	fn6 = function(n)
		if #t3 < n then
			fn7()
			return
		end
		fn6(n + 1)
		local flag = true

		while flag do
			flag = false

			for _, v in ipairs(t3[n]) do
				if fn3(v) then
					fn6(n + 1)
					emit(4, v)
					flag = true
					break
				end
			end

			continue
		end
	end

	local fn8

	local function fn9()
		local tok = toks[idx]
		local flag = fn3("let")

		if not flag then
			flag = tok.kind == "word"

			if flag then
				flag = toks[idx + 1].text == "="
			end
		end

		if flag then
			local text = toks[idx].text
			idx = 1 + idx
			fn4("=")
			fn6(1)
			local emit2 = emit
			emit2(3, fn5(text, tok.text == "let"))
		elseif fn3("out") then
			fn6(1)
			emit(8)
		elseif fn3("while") then
			local n = #t5 + 1
			fn6(1)
			fn4("do")
			local n2 = emit(7, 0)
			fn8()
			fn4("end")
			emit(6, n)
			t5[n2][2] = #t5 + 1
		elseif fn3("if") then
			fn6(1)
			fn4("then")
			local n3 = emit(7, 0)
			fn8()

			if fn3("else") then
				local n4 = emit(6, 0)
				t5[n3][2] = #t5 + 1
				fn8()
				t5[n4][2] = #t5 + 1
			else
				t5[n3][2] = #t5 + 1
			end

			fn4("end")
		else
			fail("unexpected '" .. tostring(tok.text) .. "'")
		end
	end

	fn8 = function()
		while (toks[idx].kind ~= "end" and toks[idx].text ~= "end") and toks[idx].text ~= "else" do
			fn9()
		end
	end

	for k, v in pairs(t4) do
		emit(1, v)
		local emit2 = emit
		emit2(3, fn5(k, true))
	end

	fn8()

	if not (toks[idx].kind == "end") then
		fail("trailing '" .. tostring(toks[idx].text) .. "'")
	end

	emit(9)
	return t5, cnt
end

local function fn3(t4, n, n2)
	local buf = {}

	for i = n, math.min(n2, #t4) do
		local v = t4[i][1]
		local v2 = t4[i][2]
		local s = t[v]
		table.insert(buf, string.format("%3d %-6s %s", i, s, (v2 == nil and "") or tostring(v2)))
	end

	return table.concat(buf, "\n")
end

local function fn4(t4, max)
	local t5 = {}
	local t6 = {}
	local t7 = {}
	local idx = 0
	local t8 = {}
	local idx2 = 1
	local cnt = 0

	local ok, err = pcall(function()
		repeat
			local op = t4[idx2][1]
			local v = t4[idx2][2]
			cnt += 1
			t8[(cnt - 1) % 4 + 1] = idx2

			if cnt > max then
				error({ kind = "step limit", line = 0, message = "more than " .. max .. " steps" },
					0)
			end

			idx2 += 1

			if op == 1 then
				idx += 1
				t5[idx] = v
			elseif op == 2 then
				idx += 1
				t5[idx] = t6[v]
			elseif op == 3 then
				local v2 = t5[idx]
				local n = idx - 1
				t6[v] = v2
				idx = n
			elseif op == 4 then
				t5[idx - 1] = t2[v](t5[idx - 1], t5[idx])
				idx -= 1
			elseif op == 5 then
				t5[idx] = -t5[idx]
			elseif op == 6 then
				idx2 = v
			elseif op == 7 then
				if t5[idx] == 0 then
					idx2 = v
				end

				idx -= 1
			elseif op == 8 then
				table.insert(t7, tostring(t5[idx]))
				idx -= 1
			end
		until op == 9
	end)

	local buf = {}
	local n = cnt

	for i = n, math.max(1, cnt - 3), -1 do
		table.insert(buf, tostring(t8[(i - 1) % 4 + 1]))
	end

	local n2 = cnt
	return ok, err, t7, n2, table.concat(buf, "<")
end

local t4 = {
	{
		"fibonacci",
		2000,
		[[let a = 0
let b = 1
let i = 0
while i < n + 5 do
 let t = a + b
 a = b
 b = t
 i = i + 1
end
out a]],
	},
	{
		"gcd",
		2000,
		[[let x = 84 * n
let y = 36 + n
while y > 0 do
 let r = x % y
 x = y
 y = r
end
out x
out 84 * n * (36 + n) / x]],
	},
	{
		"collatz",
		2000,
		[[let c = 6 + n * 3
let s = 0
while c > 1 do
 if c % 2 == 0 then c = c / 2 else c = 3 * c + 1 end
 s = s + 1
end
out s]],
	},
	{
		"primes",
		4000,
		[[let p = 2
while p < 12 + n * 4 do
 let d = 2
 let q = 1
 while d * d < p + 1 do
  if p % d == 0 then q = 0 end
  d = d + 1
 end
 if q == 1 then out p end
 p = p + 1
end]],
	},
	{ "divide", 100, "let z = n - n\nout 7 - -n\nout 10 / z" },
	{ "spin", 250, "let k = 0\nwhile 1 do k = k + 1 end" },
	{ "broken", 100, "let v = (n + 2\nout v" },
	{ "unknown", 100, "out w + 1" },
}

return function(n)
	local buf = {}
	local s

	for _, t5 in ipairs(t4) do
		local v = t5[1]
		local n2 = t5[2]
		local v2 = t5[3]
		local ok, res, res2 = pcall(fn2, v2, { n = n })

		if not ok then
			table.insert(buf, string.format("%-9s compile error (%s) line %d: %s",
				v, res.kind, res.line, res.message))
		else
			local flag, err, t6, n3, s2 = fn4(res, n2 + n * 10)
			s = "ok"

			if (not flag and type(err) == "table") then
				s = err.kind .. ": " .. err.message
			elseif not flag then
				s = "error: " .. err
			end

			table.insert(buf, string.format("%-9s %2d ops %d slots %4d steps [%s] %s, trace %s",
				v, #res, res2, n3, table.concat(t6, " "), s, s2))

			if v == "collatz" then
				table.insert(buf, fn3(res, 5 + n, 9 + n))
			end
		end
	end

	return table.concat(buf, "\n")
end
