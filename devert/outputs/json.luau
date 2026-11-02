local fn, f
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

local t3 = { ["\""] = "\"", ["\\"] = "\\", ["/"] = "/",
	b = "\x08", f = "\x0c", n = "\n", r = "\r", t = "\t" }
local t4 = { { "true", true }, { "false", false }, { "null", null } }

local function fn2(s)
	return (string.gsub(s, "[%c\"\\]", function(s2)
		return t2[s2] or string.format("\\u%04x", string.byte(s2))
	end))
end

local function fn3(t5)
	local cnt = 0

	for _ in pairs(t5) do
		cnt += 1
	end

	local len = #t5
	return cnt == len, cnt
end

fn = function(v, s, n)
	local kind = type(v)
	if v == null then
		return "null"
	end

	if kind == "boolean" then
		if v then
			local s2 = "true"
			return s2
		end
		return "false"
	end

	if kind == "number" then
		if not (v ~= v or v == math.huge) then
			if not (v == -math.huge) then
				if v == math.floor(v) then
					if math.abs(v) < 1000000000000000 then
						return string.format("%d", v)
					end
				end

				return string.format("%.14g", v)
			end
		end

		error({ reason = "number cannot be encoded", detail = tostring(v) }, 0)
		return string.format("%.14g", v)
	end

	if kind == "string" then
		return "\"" .. fn2(v) .. "\""
	end

	if not (kind == "table") then
		error({ reason = "unsupported type", detail = kind }, 0)
	end

	local n2 = n or 0

	if n2 > 20 then
		error({ reason = "nesting too deep", detail = tostring(n2) }, 0)
	end

	local s3 = ""
	local s4 = ""
	local s5 = ""

	if not (s == nil) then
		string.rep(s, n2)
		local pad = string.rep(s, n2 + 1)
		s3 = "\n"
		s5 = pad
	end

	local buf = {}
	local flag, n3 = fn3(v)

	if flag then
		if n3 == 0 then
			return "[]"
		end

		for i = 1, n3 do
			local s6 = fn(v[i], s, n2 + 1)
			buf[i] = s5 .. s6
		end

		local s7 = table.concat(buf, "," .. s3)
		local s8 = s4 .. "]"
		local s9 = s7 .. s3 .. s8
		return "[" .. s3 .. s9
	end

	local keys = {}

	for k in pairs(v) do
		if not (type(k) == "string") then
			error({ reason = "object key is not a string", detail = tostring(k) }, 0)
		end

		table.insert(keys, k)
	end

	table.sort(keys)
	local s10 = if s ~= nil then ": " else ":"

	for i, key in ipairs(keys) do
		local s11 = "\"" .. fn2(key) .. "\"" .. s10 .. fn(v[key], s, n2 + 1)
		buf[i] = s5 .. s11
	end

	local s12 = table.concat(buf, "," .. s3)
	local s13 = s4 .. "}"
	local s14 = s12 .. s3 .. s13
	return "{" .. s3 .. s14
end

local function fn4(n)
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

				table.insert(buf, fn4(n2))
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
	if self:peek() == "}" then
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

local function fn5(text)
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

local function fn6(n)
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
	}

	t7.empty = {}
	t7.missing = null
	t7.nested = { level = 1, child = { level = 2, child = { level = 3, note = "deep" } } }
	return t7
end

return function(n)
	local buf = {}
	local t7 = fn6(n)
	local text = fn(t7)
	local t8 = fn5(text)
	table.insert(buf, text)
	table.insert(buf, string.format("round trip %s, deep equal %s, missing is %s, %d bytes",
		tostring(fn(t8) == text), tostring(f(t7, t8)), tostring(t8.missing), #text))
	local s = fn(t8, "  ")
	local s2, cnt = string.gsub(s, "\n", "\n")
	table.insert(buf, string.format("pretty: %d lines, %d bytes; head: %s",
		cnt + 1, #s, string.sub(s, 1, 40 + n * 8)))
	local fn7 = fn5
	local v = fn7(string.format("{\"n\": %d, \"list\": [1, -2.5e%d, 3E2, true, null, \"caf\\u00e9 \\u20ac\"], \"s\": \"a\\/b\"}",
		n, n % 3))
	table.insert(buf, fn(v))

	for i, s3 in ipairs(t6) do
		local ok, res = pcall(fn5, s3)
		table.insert(buf, (ok and string.format("malformed %d decoded as %s", i, fn(res)))
			or string.format("malformed %d: %s %s", i, res.reason, res.detail))
	end

	local t9 = {}
	t9.self = t9
	local t10 = { { x = 3, 1, 2 }, t9, { value = math.huge }, { f = f } }

	for _, t11 in ipairs(t10) do
		local ok, res = pcall(fn, t11)
		table.insert(buf, (ok and "encoded unexpectedly")
			or "encode error: " .. res.reason .. " (" .. res.detail .. ")")
	end

	return table.concat(buf, "\n")
end
