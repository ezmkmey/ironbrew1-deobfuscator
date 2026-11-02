local function fn(s)
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

	if not (token.kind ~= "name") then
		if (self:peek()).value == "(" then
			self:advance()
			return { tag = "call", name = token.value, args = self:arguments(), pos = token.pos }
		end
		return { tag = "var", name = token.value, pos = token.pos }
	end

	if token.value == "-" then
		return { tag = "neg", operand = self:expression(9) }
	end

	if token.value == "(" then
		local expr = self:expression(0)
		local token2 = self:advance()

		if not (token2.value == ")") then
			error({ code = "expected", pos = token2.pos, text = ")" }, 0)
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

local function fn2()
	local t3 = {}
	local cnt = 0

	local function fn3(t4)
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
					error({ code = "undefined", pos = t4.pos, text = t4.name }, 0)
				end

				return v
			end
		end

		if tag == "assign" then
			local name = t4.name
			local val2 = fn3(t4.value)

			return function()
				local v = val2()
				t3[name] = v
				return v
			end
		end

		if not (tag ~= "neg") then
			local opnd = fn3(t4.operand)

			return function()
				return -opnd()
			end
		end

		if tag == "call" then
			local fn4 = t2[t4.name]

			if fn4 == nil then
				error({ code = "unknown_function", pos = t4.pos, text = t4.name }, 0)
			end

			local fns = {}

			for i, arg in ipairs(t4.args) do
				fns[i] = fn3(arg)
			end

			return function()
				local t5 = {}

				for i, f in ipairs(fns) do
					t5[i] = f()
				end

				return fn4(table.unpack(t5, 1, #fns))
			end
		end

		local op = t4.op
		local left = fn3(t4.left)
		local right = fn3(t4.right)

		return function()
			local n = left()
			local n2 = right()
			cnt += 1
			if op == "+" then
				return n + n2
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
						return if n < n2 then 1 else 0
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
		local obj = cls.new(fn(s))
		local expr = obj:expression(0)
		local token = obj:peek()

		if token.kind ~= "eof" then
			error({ code = "trailing", pos = token.pos, text = tostring(token.value) }, 0)
		end

		return (fn3(expr))()
	end, function()
		return cnt
	end, t3
end

local function fn3(n)
	if n == math.floor(n) then
		if math.abs(n) < 1000000000000 then
			return string.format("%d", n)
		end
	end

	return string.format("%.6g", n)
end

local t3 = { "+", "-", "*", "/", "%", "^", "<" }
local t4 = { "x", "y", "z", "w" }

local function fn4(t5, n)
	t5.seed = t5.seed * 16807 % 2147483647
	local op = t5.seed % 10

	if (n <= 0 or op < 3) then
		if op == 1 then
			return tostring(t5.seed % 20)
		end
		return t4[t5.seed % #t4 + 1]
	end

	if op == 3 then
		return "-" .. fn4(t5, n - 1)
	end

	if op == 4 then
		return "max(" .. fn4(t5, n - 1) .. ", " .. fn4(t5, n - 1) .. ")"
	end
	local s = t3[t5.seed % #t3 + 1]
	if s == "^" then
		return "(" .. fn4(t5, n - 1) .. ")^" .. tostring(t5.seed % 3)
	end
	return "(" .. fn4(t5, n - 1) .. " " .. s .. " " .. fn4(t5, n - 1) .. ")"
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
	local fn5, fn6, t6 = fn2()
	t6.n = n
	local buf = {}
	local cnt = 0

	local function fn7(s)
		local ok, res = pcall(fn5, s)

		if ok then
			table.insert(buf, string.format("%-26s = %s", s, fn3(res)))
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
		fn7(s)
	end

	local t7 = { seed = n * 7919 + 17 }

	for _ = 1, 4 + n do
		fn7(fn4(t7, 3))
	end

	local buf2 = {}
	local v, v2, v3 = pairs(t6)
	local s2 = "="

	for k, v4 in v, v2, v3 do
		s2 ..= fn3(v4)
		table.insert(buf2, k .. s2)
	end

	table.sort(buf2, function(a, b)
		return a < b
	end)

	local n2 = #buf - cnt
	local n3 = cnt
	table.insert(buf, string.format("ok=%d failed=%d operations=%d", n2, n3, fn6()))
	table.insert(buf, table.concat(buf2, " "))
	return table.concat(buf, "\n")
end
