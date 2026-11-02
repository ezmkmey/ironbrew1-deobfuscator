
local null = setmetatable({}, { __tostring = function() return "null" end })

local ESCAPES = { ["\""] = "\\\"", ["\\"] = "\\\\", ["\b"] = "\\b", ["\f"] = "\\f", ["\n"] = "\\n", ["\r"] = "\\r", ["\t"] = "\\t" }
local UNESCAPES = { ["\""] = "\"", ["\\"] = "\\", ["/"] = "/", b = "\b", f = "\f", n = "\n", r = "\r", t = "\t" }
local LITERALS = { { "true", true }, { "false", false }, { "null", null } }

local function escapeString(text)
	return (string.gsub(text, "[%c\"\\]", function(char)
		return ESCAPES[char] or string.format("\\u%04x", string.byte(char))
	end))
end

local function isArray(value)
	local count = 0
	for _ in pairs(value) do
		count += 1
	end
	return count == #value, count
end

local function encode(value, indent, depth)
	local kind = type(value)
	if value == null then
		return "null"
	elseif kind == "boolean" then
		return value and "true" or "false"
	elseif kind == "number" then
		if value ~= value or value == math.huge or value == -math.huge then
			error({ reason = "number cannot be encoded", detail = tostring(value) }, 0)
		elseif value == math.floor(value) and math.abs(value) < 1e15 then
			return string.format("%d", value)
		end
		return string.format("%.14g", value)
	elseif kind == "string" then
		return "\"" .. escapeString(value) .. "\""
	elseif kind ~= "table" then
		error({ reason = "unsupported type", detail = kind }, 0)
	end
	depth = depth or 0
	if depth > 20 then
		error({ reason = "nesting too deep", detail = tostring(depth) }, 0)
	end
	local newline, pad, padInner = "", "", ""
	if indent ~= nil then
		newline, pad, padInner = "\n", string.rep(indent, depth), string.rep(indent, depth + 1)
	end
	local parts = {}
	local array, count = isArray(value)
	if array then
		if count == 0 then
			return "[]"
		end
		for index = 1, count do
			parts[index] = padInner .. encode(value[index], indent, depth + 1)
		end
		return "[" .. newline .. table.concat(parts, "," .. newline) .. newline .. pad .. "]"
	end
	local keys = {}
	for key in pairs(value) do
		if type(key) ~= "string" then
			error({ reason = "object key is not a string", detail = tostring(key) }, 0)
		end
		table.insert(keys, key)
	end
	table.sort(keys)
	local separator = indent ~= nil and ": " or ":"
	for index, key in ipairs(keys) do
		parts[index] = padInner .. "\"" .. escapeString(key) .. "\"" .. separator .. encode(value[key], indent, depth + 1)
	end
	return "{" .. newline .. table.concat(parts, "," .. newline) .. newline .. pad .. "}"
end

local function utf8Char(code)
	if code < 128 then
		return string.char(code)
	elseif code < 2048 then
		return string.char(192 + math.floor(code / 64), 128 + code % 64)
	end
	return string.char(224 + math.floor(code / 4096), 128 + math.floor(code / 64) % 64, 128 + code % 64)
end

local Decoder = {}
Decoder.__index = Decoder

function Decoder.new(text)
	return setmetatable({ text = text, pos = 1 }, Decoder)
end

function Decoder:fail(reason)
	error({ reason = reason, detail = "at " .. self.pos }, 0)
end

function Decoder:skip()
	self.pos = select(2, string.find(self.text, "^[ \t\r\n]*", self.pos)) + 1
end

function Decoder:peek()
	return string.sub(self.text, self.pos, self.pos)
end

function Decoder:literal()
	for _, entry in ipairs(LITERALS) do
		local word = entry[1]
		if string.sub(self.text, self.pos, self.pos + #word - 1) == word then
			self.pos += #word
			return entry[2]
		end
	end
	self:fail("unexpected character '" .. self:peek() .. "'")
end

function Decoder:number()
	local first, last = string.find(self.text, "^-?%d+%.?%d*[eE]?[-+]?%d*", self.pos)
	local value = first and tonumber(string.sub(self.text, first, last))
	if value == nil then
		self:fail("malformed number")
	end
	self.pos = last + 1
	return value
end

function Decoder:string()
	local text, pos, parts = self.text, self.pos + 1, {}
	while true do
		local first = string.find(text, "[\"\\]", pos)
		if first == nil then
			self.pos = #text + 1
			self:fail("unterminated string")
		end
		table.insert(parts, string.sub(text, pos, first - 1))
		if string.byte(text, first) == 34 then
			self.pos = first + 1
			return table.concat(parts)
		end
		local escape = string.sub(text, first + 1, first + 1)
		if escape == "u" then
			local code = tonumber(string.sub(text, first + 2, first + 5), 16)
			if code == nil then
				self.pos = first
				self:fail("bad unicode escape")
			end
			table.insert(parts, utf8Char(code))
			pos = first + 6
		elseif UNESCAPES[escape] ~= nil then
			table.insert(parts, UNESCAPES[escape])
			pos = first + 2
		else
			self.pos = first
			self:fail("bad escape '\\" .. escape .. "'")
		end
	end
end

function Decoder:array()
	local result = {}
	self.pos += 1
	self:skip()
	if self:peek() == "]" then
		self.pos += 1
		return result
	end
	repeat
		table.insert(result, self:value())
		self:skip()
		local char = self:peek()
		if char ~= "," and char ~= "]" then
			self:fail("expected ',' or ']'")
		end
		self.pos += 1
	until char == "]"
	return result
end

function Decoder:object()
	local result = {}
	self.pos += 1
	self:skip()
	if self:peek() == "}" then
		self.pos += 1
		return result
	end
	while true do
		self:skip()
		if self:peek() ~= "\"" then
			self:fail("expected a string key")
		end
		local key = self:string()
		self:skip()
		if self:peek() ~= ":" then
			self:fail("expected ':'")
		end
		self.pos += 1
		result[key] = self:value()
		self:skip()
		local char = self:peek()
		self.pos += 1
		if char == "}" then
			break
		elseif char ~= "," then
			self:fail("expected ',' or '}'")
		end
	end
	return result
end

function Decoder:value()
	self:skip()
	local char = self:peek()
	if char == "{" then
		return self:object()
	elseif char == "[" then
		return self:array()
	elseif char == "\"" then
		return self:string()
	elseif char == "-" or string.find(char, "^%d") then
		return self:number()
	end
	return self:literal()
end

local function decode(text)
	local decoder = Decoder.new(text)
	local value = decoder:value()
	decoder:skip()
	if decoder.pos <= #text then
		decoder:fail("trailing characters")
	end
	return value
end

local function deepEqual(a, b)
	if type(a) ~= "table" or type(b) ~= "table" then
		return a == b
	end
	for key, value in pairs(a) do
		if not deepEqual(value, b[key]) then
			return false
		end
	end
	for key in pairs(b) do
		if a[key] == nil then
			return false
		end
	end
	return true
end

local WORDS = { "alpha", "beta", "gamma", "tab\there", "quote\"d", "back\\slash", "line\nbreak", "caf\195\169", "bell\7" }
local MALFORMED = { "{\"a\": 1,}", "[1, 2", "\"abc", "{\"x\": tru}", "[1, \"\\q\"]", "{\"k\" 5}", "[1] 2", "-", "[\"\\u12G4\"]" }

local function buildDocument(n)
	local tags, metrics, matrix = {}, {}, {}
	for index = 1, n + 2 do
		table.insert(tags, WORDS[(n * index) % #WORDS + 1])
	end
	for index = 1, 4 do
		metrics["m" .. index] = (n * index * 7 % 13) / 4 - 1
	end
	for row = 1, 3 do
		matrix[row] = {}
		for column = 1, 3 do
			matrix[row][column] = (row - column) * n + column ^ 2
		end
	end
	return {
		id = n, name = WORDS[n % #WORDS + 1], active = n % 2 == 0, ratio = n / 8, tags = tags,
		metrics = metrics, matrix = matrix, empty = {}, missing = null,
		nested = { level = 1, child = { level = 2, child = { level = 3, note = "deep" } } },
	}
end

return function(n)
	local lines, document = {}, buildDocument(n)
	local compact = encode(document)
	local decoded = decode(compact)
	table.insert(lines, compact)
	table.insert(lines, string.format("round trip %s, deep equal %s, missing is %s, %d bytes",
		tostring(encode(decoded) == compact), tostring(deepEqual(document, decoded)), tostring(decoded.missing), #compact))
	local pretty = encode(decoded, "  ")
	local _, breaks = string.gsub(pretty, "\n", "\n")
	table.insert(lines, string.format("pretty: %d lines, %d bytes; head: %s", breaks + 1, #pretty, string.sub(pretty, 1, 40 + n * 8)))
	local sample = decode(string.format(
		"{\"n\": %d, \"list\": [1, -2.5e%d, 3E2, true, null, \"caf\\u00e9 \\u20ac\"], \"s\": \"a\\/b\"}", n, n % 3))
	table.insert(lines, encode(sample))
	for index, text in ipairs(MALFORMED) do
		local ok, problem = pcall(decode, text)
		table.insert(lines, ok and string.format("malformed %d decoded as %s", index, encode(problem))
			or string.format("malformed %d: %s %s", index, problem.reason, problem.detail))
	end
	local loop = {}
	loop.self = loop
	for _, bad in ipairs({ { 1, 2, x = 3 }, loop, { value = math.huge }, { f = deepEqual } }) do
		local ok, problem = pcall(encode, bad)
		table.insert(lines, ok and "encoded unexpectedly" or ("encode error: " .. problem.reason .. " (" .. problem.detail .. ")"))
	end
	return table.concat(lines, "\n")
end
