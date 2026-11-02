local function fn()
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
			return (n2 < n and 1) or 0
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

	local function fn2(s)
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

	local function fn3(s, t4)
		local toks = fn2(s)
		local idx = 1
		local t5 = {}
		local t6 = {}
		local cnt = 0

		local function emit(n, v)
			table.insert(t5, { n, v })
			return #t5
		end

		local function fail(msg)
			local t7 = { kind = "syntax" }
			t7.line = toks[idx].line
			t7.message = msg
			error(t7, 0)
		end

		local function fn4(v)
			if toks[idx].text == v then
				idx += 1
				return true
			end
			return false
		end

		local function fn5(s2)
			if not fn4(s2) then
				fail("expected '" .. s2 .. "' near '" .. tostring(toks[idx].text) .. "'")
			end
		end

		local function fn6(s2, flag)
			if t6[s2] == nil then
				if not flag then
					fail("undeclared variable '" .. s2 .. "'")
				end

				cnt += 1
				t6[s2] = cnt
			end

			return t6[s2]
		end

		local fn7

		local function fn8()
			local tok = toks[idx]
			idx += 1

			if tok.kind == "number" then
				emit(1, tok.text)
			elseif tok.text == "(" then
				fn7(1)
				fn5(")")
			elseif tok.text == "-" then
				fn8()
				emit(5)
			elseif (tok.kind == "word" and string.find(tok.text, "^%a")) then
				local emit2 = emit
				emit2(2, fn6(tok.text, false))
			else
				idx -= 1
				fail("unexpected '" .. tostring(tok.text) .. "'")
			end
		end

		fn7 = function(n)
			if #t3 < n then
				fn8()
				return
			end
			fn7(n + 1)
			local flag = true

			while flag do
				flag = false

				for _, v in ipairs(t3[n]) do
					if fn4(v) then
						fn7(n + 1)
						emit(4, v)
						flag = true
						break
					end
				end

				continue
			end
		end

		local fn9

		local function fn10()
			local tok = toks[idx]
			local flag = fn4("let")

			if not flag then
				flag = tok.kind == "word"

				if flag then
					flag = toks[idx + 1].text == "="
				end
			end

			if flag then
				local text = toks[idx].text
				idx += 1
				fn5("=")
				fn7(1)
				local emit2 = emit
				emit2(3, fn6(text, tok.text == "let"))
			elseif fn4("out") then
				fn7(1)
				emit(8)
			elseif fn4("while") then
				local n = #t5 + 1
				fn7(1)
				fn5("do")
				local n2 = emit(7, 0)
				fn9()
				fn5("end")
				emit(6, n)
				t5[n2][2] = #t5 + 1
			elseif fn4("if") then
				fn7(1)
				fn5("then")
				local n3 = emit(7, 0)
				fn9()

				if fn4("else") then
					local n4 = emit(6, 0)
					t5[n3][2] = #t5 + 1
					fn9()
					t5[n4][2] = #t5 + 1
				else
					t5[n3][2] = #t5 + 1
				end

				fn5("end")
			else
				fail("unexpected '" .. tostring(tok.text) .. "'")
			end
		end

		fn9 = function()
			while (toks[idx].kind ~= "end" and toks[idx].text ~= "end")
				and toks[idx].text ~= "else" do
				fn10()
			end
		end

		for k, v in pairs(t4) do
			emit(1, v)
			local emit2 = emit
			emit2(3, fn6(k, true))
		end

		fn9()

		if not (toks[idx].kind == "end") then
			fail("trailing '" .. tostring(toks[idx].text) .. "'")
		end

		emit(9)
		return t5, cnt
	end

	local function fn4(t4, n, n2)
		local buf = {}

		for i = n, math.min(n2, #t4) do
			local v = t4[i][1]
			local v2 = t4[i][2]
			local s = t[v]
			table.insert(buf,
				string.format("%3d %-6s %s", i, s, (v2 == nil and "") or tostring(v2)))
		end

		return table.concat(buf, "\n")
	end

	local function fn5(t4, max)
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
					error({ kind = "step limit", line = 0,
						message = "more than " .. max .. " steps" }, 0)
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
			local ok, res, res2 = pcall(fn3, v2, { n = n })

			if not ok then
				table.insert(buf, string.format("%-9s compile error (%s) line %d: %s",
					v, res.kind, res.line, res.message))
			else
				local flag, err, t6, n3, s2 = fn5(res, n2 + n * 10)
				s = "ok"

				if (not flag and type(err) == "table") then
					s = err.kind .. ": " .. err.message
				elseif not flag then
					s = "error: " .. err
				end

				table.insert(buf, string.format("%-9s %2d ops %d slots %4d steps [%s] %s, trace %s",
					v, #res, res2, n3, table.concat(t6, " "), s, s2))

				if v == "collatz" then
					table.insert(buf, fn4(res, 5 + n, 9 + n))
				end
			end
		end

		return table.concat(buf, "\n")
	end
end

local fn2 = fn()

local function fn3()
	local function fn4(s)
		local toks = {}
		local pos = 1
		local n

		while pos <= #s do
			local byte = string.byte(s, pos)

			if (byte == 32 or byte == 9) then
				pos += 1
			else
				local first, last = string.find(s, "^%d+%.?%d*", pos)
				n = last

				if first == nil then
					local first2, last2 = string.find(s, "^[%a_][%w_]*", pos)
					n = last2

					if first2 == nil then
						local ch = string.char(byte)

						if string.find("+-*/%^(),=<>", ch, 1, true) == nil then
							error({ code = "bad_char", pos = pos, text = ch }, 0)
						end

						n = pos
						table.insert(toks, { kind = "op", value = ch, pos = pos })
					else
						table.insert(toks,
							{ kind = "name", value = string.sub(s, first2, n), pos = pos })
					end
				else
					table.insert(toks,
						{ kind = "number", value = tonumber(string.sub(s, first, n)), pos = pos })
				end

				pos = n + 1
			end
		end

		table.insert(toks, { kind = "eof", value = "<eof>", pos = #s + 1 })
		return toks
	end

	local t = {
		["="] = { 2, 1 },
		["<"] = { 3, 4 },
		[">"] = { 3, 4 },
		["+"] = { 5, 6 },
		["-"] = { 5, 6 },
		["*"] = { 7, 8 },
		["/"] = { 7, 8 },
		["%"] = { 7, 8 },
		["^"] = { 12, 11 },
	}

	local cls = {}
	cls.__index = cls

	cls.new = function(toks)
		return setmetatable({ tokens = toks, index = 1 }, cls)
	end

	cls.peek = function(self)
		return self.tokens[self.index]
	end

	cls.advance = function(self)
		local token = self.tokens[self.index]
		self.index += 1
		return token
	end

	cls.arguments = function(self)
		local exprs = {}
		if (self:peek()).value == ")" then
			self:advance()
			return exprs
		end

		repeat
			table.insert(exprs, self:expression(0))
			local token = self:advance()

			if (token.value ~= "," and token.value ~= ")") then
				error({ code = "expected", pos = token.pos, text = ", or )" }, 0)
			end
		until token.value == ")"

		return exprs
	end

	cls.primary = function(self)
		local token = self:advance()
		if token.kind == "number" then
			return { tag = "num", value = token.value }
		end

		if token.kind == "name" then
			if (self:peek()).value == "(" then
				self:advance()

				return {
					tag = "call",
					name = token.value,
					args = self:arguments(),
					pos = token.pos,
				}
			end

			return { tag = "var", name = token.value, pos = token.pos }
		end

		if token.value == "-" then
			return { tag = "neg", operand = self:expression(9) }
		end

		if token.value == "(" then
			local expr = self:expression(0)
			local token2 = self:advance()

			if token2.value ~= ")" then
				local t2 = { code = "expected" }
				t2.pos = token2.pos
				t2.text = ")"
				error(t2, 0)
			end

			return expr
		end

		error({ code = "unexpected", pos = token.pos, text = tostring(token.value) }, 0)
	end

	cls.expression = function(self, n)
		local left = self:primary()

		while true do
			local token = self:peek()
			local t2 = t[token.value]
			local done = (token.kind ~= "op" or t2 == nil) or t2[1] < n

			if done then
				break
			else
				self:advance()
				local v = self.expression(self, t2[2])

				if token.value == "=" then
					if not (left.tag == "var") then
						error({ code = "assign_target", pos = token.pos, text = left.tag }, 0)
					end

					left = { tag = "assign", name = left.name, value = v }
				else
					left = { tag = "binary", op = token.value, left = left, right = v }
				end
			end
		end

		return left
	end

	local t2 = {}

	t2.max = function(...)
		local cnt = select("#", ...)

		if cnt == 0 then
			error("max needs at least one argument", 0)
		end

		local v = ...
		local n = v

		for i = 2, cnt do
			local n2 = select(i, ...)

			if n < n2 then
				n = n2
			end
		end

		return n
	end

	t2.avg = function(...)
		local cnt = select("#", ...)
		local sum = 0

		for _, n in ipairs({ ... }) do
			sum += n
		end

		if cnt == 0 then
			error({ code = "arity", pos = 0, text = "avg needs arguments" }, 0)
		end

		return sum / cnt
	end

	local function fn5()
		local t3 = {}
		local cnt = 0

		local function fn6(t4)
			local tag = t4.tag

			if tag == "num" then
				local val = t4.value

				return function(...)
					return val
				end
			end

			if tag == "var" then
				return function()
					local v = t3[t4.name]

					if v == nil then
						local t5 = { code = "undefined" }
						t5.pos = t4.pos
						t5.text = t4.name
						error(t5, 0)
					end

					return v
				end
			end

			if tag == "assign" then
				local name = t4.name
				local val2 = fn6(t4.value)

				return function()
					local v = val2()
					t3[name] = v
					return v
				end
			end

			if tag == "neg" then
				local opnd = fn6(t4.operand)

				return function()
					return -opnd()
				end
			end

			if tag == "call" then
				local fn7 = t2[t4.name]

				if fn7 == nil then
					error({ code = "unknown_function", pos = t4.pos, text = t4.name }, 0)
				end

				local fns = {}

				for i, arg in ipairs(t4.args) do
					fns[i] = fn6(arg)
				end

				return function()
					local t5 = {}

					for i, f in ipairs(fns) do
						t5[i] = f()
					end

					return fn7(table.unpack(t5, 1, #fns))
				end
			end

			local op = t4.op
			local left = fn6(t4.left)
			local right = fn6(t4.right)

			return function()
				local n = left()
				local n2 = right()
				cnt += 1
				if op == "+" then
					return n2 + n
				end

				if op == "-" then
					return n - n2
				end

				if op == "*" then
					return n * n2
				end

				if not (op == "/") then
					if not (op == "%") then
						if op == "^" then
							return n ^ n2
						end

						if op == "<" then
							return (n < n2 and 1) or 0
						end
						return (n2 < n and 1) or 0
					end
				end

				if n2 == 0 then
					error("division by zero in '" .. op .. "'", 0)
				end

				if op == "/" then
					local n3 = n / n2
					if n3 then
						return n3
					end
				end

				return n % n2
			end
		end

		return function(s)
			local obj = cls.new(fn4(s))
			local expr = obj:expression(0)
			local token = obj:peek()

			if not (token.kind == "eof") then
				error({ code = "trailing", pos = token.pos, text = tostring(token.value) }, 0)
			end

			return (fn6(expr))()
		end, function()
			return cnt
		end, t3
	end

	local function fn6(n)
		if (n == math.floor(n) and math.abs(n) < 1000000000000) then
			return string.format("%d", n)
		end
		return string.format("%.6g", n)
	end

	local t3 = { "+", "-", "*", "/", "%", "^", "<" }
	local t4 = { "x", "y", "z", "w" }

	local function fn7(t5, n)
		t5.seed = t5.seed * 16807 % 2147483647
		local op = t5.seed % 10

		if (n <= 0 or op < 3) then
			if op == 1 then
				return tostring(t5.seed % 20)
			end
			return t4[t5.seed % #t4 + 1]
		end

		if op == 3 then
			return "-" .. fn7(t5, n - 1)
		end

		if op == 4 then
			return "max(" .. fn7(t5, n - 1) .. ", " .. fn7(t5, n - 1) .. ")"
		end
		local s = t3[t5.seed % #t3 + 1]
		if s == "^" then
			return "(" .. fn7(t5, n - 1) .. ")^" .. tostring(t5.seed % 3)
		end
		return "(" .. fn7(t5, n - 1) .. " " .. s .. " " .. fn7(t5, n - 1) .. ")"
	end

	local t5 = {
		"x = 4",
		"y = x * 2 + 1",
		"z = (x + y) * (y - x) / 3",
		"w = n % 4 + 0.5",
		"2 ^ 3 ^ 2 - -2 ^ 2",
		"10 % 4 + 7 % -3",
		"max(x, y, z, 2 ^ 5) > avg(1, 2, 3, 4, n)",
		"(x * y + n) ^ 0.5",
		"1 / (n - n)",
		"x = y = n * 3",
		"q + 1",
		"3 $ 4",
		"(1 + 2",
		"avg() + 1",
		"max()",
		"pow(2, 3)",
	}

	return function(n)
		local fn8, fn9, t6 = fn5()
		t6.n = n
		local buf = {}
		local cnt = 0

		local function fn10(s)
			local ok, res = pcall(fn8, s)

			if ok then
				table.insert(buf, string.format("%-26s = %s", s, fn6(res)))
			elseif type(res) == "table" then
				cnt += 1
				table.insert(buf,
					string.format("%-26s ! %s at %d (%s)", s, res.code, res.pos, res.text))
			else
				cnt += 1
				table.insert(buf, string.format("%-26s ! %s", s, res))
			end
		end

		for _, s in ipairs(t5) do
			fn10(s)
		end

		local t7 = { seed = n * 7919 + 17 }

		for _ = 1, 4 + n do
			fn10(fn7(t7, 3))
		end

		local buf2 = {}
		local v, v2, v3 = pairs(t6)
		local s2 = "="

		for k, v4 in v, v2, v3 do
			s2 ..= fn6(v4)
			table.insert(buf2, k .. s2)
		end

		table.sort(buf2, function(a, b)
			return a < b
		end)

		local n2 = #buf - cnt
		local n3 = cnt
		table.insert(buf, string.format("ok=%d failed=%d operations=%d", n2, n3, fn9()))
		table.insert(buf, table.concat(buf2, " "))
		return table.concat(buf, "\n")
	end
end

local fn4 = fn3()

local function fn5()
	local fn6, f
	local t = {}

	local null = setmetatable(t, { __tostring = function()
		return "null"
	end })

	local t2 = {
		["\""] = "\\\"",
		["\\"] = "\\\\",
		["\x08"] = "\\b",
		["\x0c"] = "\\f",
		["\n"] = "\\n",
		["\r"] = "\\r",
		["\t"] = "\\t",
	}

	local t3 = {
		["\""] = "\"",
		["\\"] = "\\",
		["/"] = "/",
		b = "\x08",
		f = "\x0c",
		n = "\n",
		r = "\r",
		t = "\t",
	}

	local t4 = { { "true", true }, { "false", false }, { "null", null } }

	local function fn7(s)
		return (string.gsub(s, "[%c\"\\]", function(s2)
			return t2[s2] or string.format("\\u%04x", string.byte(s2))
		end))
	end

	local function fn8(t5)
		local cnt = 0

		for _ in pairs(t5) do
			cnt += 1
		end

		local len = #t5
		return cnt == len, cnt
	end

	fn6 = function(v, s, n)
		local kind = type(v)
		if v == null then
			return "null"
		end

		if kind == "boolean" then
			return (v and "true") or "false"
		end

		if kind == "number" then
			if ((v ~= v or v == math.huge) or v == -math.huge) then
				error({ reason = "number cannot be encoded", detail = tostring(v) }, 0)
			elseif (v == math.floor(v) and math.abs(v) < 1000000000000000) then
				return string.format("%d", v)
			end

			return string.format("%.14g", v)
		end

		if kind == "string" then
			return "\"" .. fn7(v) .. "\""
		end

		if not (kind == "table") then
			error({ reason = "unsupported type", detail = kind }, 0)
		end

		local n2 = n or 0

		if n2 > 20 then
			error({ reason = "nesting too deep", detail = tostring(n2) }, 0)
		end

		local s2 = ""
		local s3 = ""
		local s4 = ""

		if not (s == nil) then
			string.rep(s, n2)
			local pad = string.rep(s, n2 + 1)
			s2 = "\n"
			s4 = pad
		end

		local buf = {}
		local flag, n3 = fn8(v)

		if flag then
			if n3 == 0 then
				return "[]"
			end

			for i = 1, n3 do
				local s5 = fn6(v[i], s, n2 + 1)
				buf[i] = s4 .. s5
			end

			local s6 = table.concat(buf, "," .. s2)
			local s7 = s3 .. "]"
			local s8 = s6 .. s2 .. s7
			return "[" .. s2 .. s8
		end

		local keys = {}

		for k in pairs(v) do
			if not (type(k) == "string") then
				error({ reason = "object key is not a string", detail = tostring(k) }, 0)
			end

			table.insert(keys, k)
		end

		table.sort(keys)
		local s9 = (s ~= nil and ": ") or ":"

		for i, key in ipairs(keys) do
			local s10 = "\"" .. fn7(key) .. "\"" .. s9 .. fn6(v[key], s, n2 + 1)
			buf[i] = s4 .. s10
		end

		local s11 = table.concat(buf, "," .. s2)
		local s12 = s3 .. "}"
		local s13 = s11 .. s2 .. s12
		return "{" .. s2 .. s13
	end

	local function fn9(n)
		if n < 128 then
			return string.char(n)
		end

		if n < 2048 then
			return string.char(192 + math.floor(n / 64), 128 + n % 64)
		end
		return string.char(224 + math.floor(n / 4096), 128 + math.floor(n / 64) % 64, 128 + n % 64)
	end

	local cls = {}
	cls.__index = cls

	cls.new = function(text)
		return setmetatable({ text = text, pos = 1 }, cls)
	end

	cls.fail = function(self, reason)
		error({ reason = reason, detail = "at " .. self.pos }, 0)
	end

	cls.skip = function(self)
		self.pos = select(2, string.find(self.text, "^[ \t\r\n]*", self.pos)) + 1
	end

	cls.peek = function(self)
		return string.sub(self.text, self.pos, self.pos)
	end

	cls.literal = function(self)
		local t5, v

		for _, t6 in ipairs(t4) do
			t5 = t6
			local v2 = t6[1]
			v = v2
			if string.sub(self.text, self.pos, self.pos + #v2 - 1) == v2 then
				self.pos += #v
				return t5[2]
			end
		end

		self.fail(self, "unexpected character '" .. self:peek() .. "'")
	end

	cls.number = function(self)
		local first, last = string.find(self.text, "^-?%d+%.?%d*[eE]?[-+]?%d*", self.pos)
		local n = first and tonumber(string.sub(self.text, first, last))

		if n == nil then
			self:fail("malformed number")
		end

		self.pos = last + 1
		return n
	end

	cls.string = function(self)
		local pos
		local text = self.text
		local pos2 = self.pos + 1
		local buf = {}

		while true do
			pos = string.find(text, "[\"\\]", pos2)

			if pos == nil then
				self.pos = #text + 1
				self:fail("unterminated string")
			end

			local n = pos - 1
			table.insert(buf, string.sub(text, pos2, n))

			if string.byte(text, pos) == 34 then
				break
			else
				local ch = string.sub(text, pos + 1, pos + 1)

				if ch == "u" then
					local n2 = tonumber(string.sub(text, pos + 2, pos + 5), 16)

					if n2 == nil then
						self.pos = pos
						self:fail("bad unicode escape")
					end

					table.insert(buf, fn9(n2))
					pos2 = pos + 6
				elseif t3[ch] == nil then
					self.pos = pos
					self.fail(self, "bad escape '\\" .. ch .. "'")
				else
					table.insert(buf, t3[ch])
					pos2 = pos + 2
				end
			end
		end

		self.pos = pos + 1
		return table.concat(buf)
	end

	cls.array = function(self)
		local vals = {}
		self.pos += 1
		self:skip()
		if self:peek() == "]" then
			self.pos += 1
			return vals
		end

		repeat
			table.insert(vals, self:value())
			self:skip()
			local s = self:peek()

			if (s ~= "," and s ~= "]") then
				self:fail("expected ',' or ']'")
			end

			self.pos += 1
		until s == "]"

		return vals
	end

	cls.object = function(self)
		local vals = {}
		self.pos += 1
		self:skip()
		if not (self:peek() ~= "}") then
			self.pos += 1
			return vals
		end

		while true do
			self:skip()

			if not (self:peek() == "\"") then
				self:fail("expected a string key")
			end

			local s = self:string()
			self:skip()

			if not (self:peek() == ":") then
				self:fail("expected ':'")
			end

			self.pos += 1
			vals[s] = self:value()
			self:skip()
			local s2 = self:peek()
			self.pos += 1

			if s2 == "}" then
				break
			elseif not (s2 == ",") then
				self:fail("expected ',' or '}'")
			end
		end

		return vals
	end

	cls.value = function(self)
		self:skip()
		local s = self:peek()
		if s == "{" then
			return self:object()
		end

		if s == "[" then
			return self:array()
		end

		if s == "\"" then
			return self:string()
		end

		if (s == "-" or string.find(s, "^%d")) then
			return self:number()
		end
		return self:literal()
	end

	local function fn10(text)
		local obj = cls.new(text)
		local val = obj:value()
		obj:skip()

		if obj.pos <= #text then
			obj:fail("trailing characters")
		end

		return val
	end

	f = function(v, v2)
		if type(v) ~= "table" then
			return v == v2
		end

		if type(v2) == "table" then
			for k, v3 in pairs(v) do
				if not f(v3, v2[k]) then
					return false
				end
			end

			for k in pairs(v2) do
				if v[k] == nil then
					return false
				end
			end

			return true
		end

		return v == v2
	end

	local t5 = {
		"alpha",
		"beta",
		"gamma",
		"tab\there",
		"quote\"d",
		"back\\slash",
		"line\nbreak",
		"caf\xc3\xa9",
		"bell\x07",
	}

	local t6 = {
		"{\"a\": 1,}",
		"[1, 2",
		"\"abc",
		"{\"x\": tru}",
		"[1, \"\\q\"]",
		"{\"k\" 5}",
		"[1] 2",
		"-",
		"[\"\\u12G4\"]",
	}

	local function fn11(n)
		local tags = {}
		local metrics = {}
		local matrix = {}

		for i = 1, n + 2 do
			table.insert(tags, t5[n * i % #t5 + 1])
		end

		for i = 1, 4 do
			metrics["m" .. i] = n * i * 7 % 13 / 4 - 1
		end

		for i = 1, 3 do
			matrix[i] = {}

			for j = 1, 3 do
				matrix[i][j] = (i - j) * n + j ^ 2
			end
		end

		local t7 = {
			id = n,
			name = t5[n % #t5 + 1],
			active = n % 2 == 0,
			ratio = n / 8,
			tags = tags,
			metrics = metrics,
			matrix = matrix,
			empty = {},
		}

		t7.missing = null
		t7.nested = { level = 1, child = { level = 2, child = { level = 3, note = "deep" } } }
		return t7
	end

	return function(n)
		local buf = {}
		local t7 = fn11(n)
		local text = fn6(t7)
		local t8 = fn10(text)
		table.insert(buf, text)
		table.insert(buf, string.format("round trip %s, deep equal %s, missing is %s, %d bytes",
			tostring(fn6(t8) == text), tostring(f(t7, t8)), tostring(t8.missing), #text))
		local s = fn6(t8, "  ")
		local s2, cnt = string.gsub(s, "\n", "\n")
		table.insert(buf, string.format("pretty: %d lines, %d bytes; head: %s",
			cnt + 1, #s, string.sub(s, 1, 40 + n * 8)))
		local fn12 = fn10
		local v = fn12(string.format("{\"n\": %d, \"list\": [1, -2.5e%d, 3E2, true, null, \"caf\\u00e9 \\u20ac\"], \"s\": \"a\\/b\"}",
			n, n % 3))
		table.insert(buf, fn6(v))

		for i, s3 in ipairs(t6) do
			local ok, res = pcall(fn10, s3)
			table.insert(buf, (ok and string.format("malformed %d decoded as %s", i, fn6(res)))
				or string.format("malformed %d: %s %s", i, res.reason, res.detail))
		end

		local t9 = {}
		t9.self = t9
		local t10 = { { x = 3, 1, 2 }, t9, { value = math.huge }, { f = f } }

		for _, t11 in ipairs(t10) do
			local ok, res = pcall(fn6, t11)
			table.insert(buf, (ok and "encoded unexpectedly")
				or "encode error: " .. res.reason .. " (" .. res.detail .. ")")
		end

		return table.concat(buf, "\n")
	end
end

local fn6 = fn5()

local function fn7()
	local cls = {}
	cls.__index = cls

	cls.new = function(width, height)
		local cells = {}

		for i = 1, width * height do
			cells[i] = false
		end

		local t = { width = width }
		t.height = height
		t.cells = cells
		return setmetatable(t, cls)
	end

	cls.index = function(self, x, y)
		return (y - 1) % self.height * self.width + (x - 1) % self.width + 1
	end

	cls.get = function(self, x, y)
		return self.cells[self:index(x, y)]
	end

	cls.set = function(self, x, y, flag)
		self.cells[self:index(x, y)] = flag
	end

	cls.__eq = function(t, t2)
		if (t.width ~= t2.width or t.height ~= t2.height) then
			return false
		end

		for i, cell in ipairs(t.cells) do
			if t2.cells[i] == cell then
			else
				return false
			end
		end

		return true
	end

	cls.neighbours = function(self, x, y)
		local cnt = 0

		for i = -1, 1 do
			for j = -1, 1 do
				if ((j ~= 0 or i ~= 0) and self:get(x + j, y + i)) then
					cnt += 1
				end
			end
		end

		return cnt
	end

	cls.step = function(self, t)
		local obj = cls.new(self.width, self.height)
		local cnt = 0
		local cnt2 = 0
		local flag

		for y = 1, self.height do
			for x = 1, self.width do
				local cell = self:get(x, y)
				local n = self:neighbours(x, y)
				flag = false

				if cell then
					flag = t.survive[n] == true

					if not flag then
						cnt2 += 1
					end
				elseif t.born[n] then
					flag = true
					cnt += 1
				end

				obj:set(x, y, flag)
			end
		end

		return obj, cnt, cnt2
	end

	cls.population = function(self)
		local cnt = 0

		for _, cell in ipairs(self.cells) do
			if cell then
				cnt += 1
			end
		end

		return cnt
	end

	cls.render = function(self)
		local buf = {}

		for y = 1, self.height do
			local buf2 = {}

			for x = 1, self.width do
				local s = (self:get(x, y) and "#") or "."
				buf2[x] = s
			end

			buf[y] = table.concat(buf2)
		end

		return table.concat(buf, "\n")
	end

	local function fn8(obj, y)
		for x = 1, obj.width do
			if obj:get(x, y) then
				return true
			end
		end

		return false
	end

	local function fn9(obj, x)
		for y = 1, obj.height do
			if obj:get(x, y) then
				return true
			end
		end

		return false
	end

	cls.boundingBox = function(self)
		local n, n2, n3, n4

		for y = 1, self.height do
			if fn8(self, y) then
				n = y
				break
			end
		end

		if n == nil then
			return nil
		end

		for y = self.height, n, -1 do
			if fn8(self, y) then
				n2 = y
				break
			end
		end

		for x = 1, self.width do
			if fn9(self, x) then
				n3 = x
				break
			end
		end

		for x = self.width, n3, -1 do
			if fn9(self, x) then
				n4 = x
				break
			end
		end

		return n, n2, n3, n4
	end

	local function fn10(s)
		local s2, s3 = string.match(s, "^B(%d*)/S(%d*)$")

		if s2 == nil then
			error({ rule = s, reason = "expected B<digits>/S<digits>" }, 0)
		end

		local t = { name = s }
		t.born = {}
		t.survive = {}

		for i = 1, #s2 do
			t.born[string.byte(s2, i) - 48] = true
		end

		for s4 in string.gmatch(s3, "%d") do
			t.survive[tonumber(s4)] = true
		end

		return t
	end

	local t = {
		glider = ".#.|..#|###",
		blinker = "###",
		toad = ".###|###.",
		rpentomino = ".##|##.|.#.",
		block = "##|##",
		domino = "##",
	}

	local function fn11(obj, v, x, y0)
		local y = y0
		local cnt = 0

		for s in string.gmatch(t[v] .. "|", "([^|]*)|") do
			for i = 1, #s do
				if string.sub(s, i, i) == "#" then
					obj.set(obj, x + i - 1, y, true)
					cnt += 1
				end
			end

			y += 1
		end

		return cnt
	end

	local t2 = {
		{ "B3/S23", { "blinker" } },
		{ "B36/S23", { "rpentomino" } },
		{ "B3/S23", { "toad", "block", "glider" } },
		{ "B2/S", { "blinker" } },
		{ "B3/S12345", { "rpentomino", "block" } },
		{ "B3S23", { "glider" } },
		{ "B3/S23", { "domino", "glider" } },
		{ "B3/S23", { "domino" } },
	}

	local function fn12(n, t3)
		local ok, res = pcall(fn10, t3[1])
		if not ok then
			return { string.format("rule %s rejected: %s", res.rule, res.reason) }
		end
		local obj = cls.new(10, 8)
		local sum = 0

		for i, v in ipairs(t3[2]) do
			local x = 1 + (i * 3 + n) % 8
			local y = 1 + (i * 2 + n) % 6
			sum += fn11(obj, v, x, y)
		end

		local t4 = { string.format("rule %s, %d cells placed", res.name, sum) }
		local buf = { obj:population() }
		local t5 = { [obj:render()] = 0 }
		local births = 0
		local deaths = 0

		for i = 1, n + 3 do
			local t6, n2, n3 = obj:step(res)
			births += n2
			deaths += n3

			if t6 == obj then
				table.insert(t4, string.format("still life after %d generations", i - 1))
				break
			else
				obj = t6
				table.insert(buf, t6:population())
				local s = obj:render()

				if t5[s] == nil then
					t5[s] = i
				else
					table.insert(t4,
						string.format("cycle of period %d at generation %d", i - t5[s], i))
					break
				end
			end
		end

		table.insert(t4, string.format("population %s; births %d deaths %d",
			table.concat(buf, " "), births, deaths))
		local n4, n5, n6, n7 = obj:boundingBox()

		if n4 == nil then
			table.insert(t4, "extinct")
		else
			table.insert(t4, string.format("box rows %d-%d columns %d-%d", n4, n5, n6, n7))
			table.insert(t4, obj:render())
		end

		return t4
	end

	return function(n)
		local buf = {}
		local t3 = { 0, 3 }

		for _, n2 in ipairs(t3) do
			local t4 = t2[(n + n2 - 1) % #t2 + 1]

			for _, v in ipairs(fn12(n, t4)) do
				table.insert(buf, v)
			end
		end

		return table.concat(buf, "\n")
	end
end

local fn8 = fn7()

return function(v)
	local t = {
		"stackvm\n" .. fn2(v),
		"calc\n" .. fn4(v),
		"json\n" .. fn6(v),
		"life\n" .. fn8(v),
	}

	return table.concat(t, "\n")
end
