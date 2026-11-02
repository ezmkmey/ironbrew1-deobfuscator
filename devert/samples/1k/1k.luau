local bench_stackvm = (function()

local PUSH, LOAD, STORE, BINARY, NEG, JUMP, JUMP_FALSE, OUT, HALT = 1, 2, 3, 4, 5, 6, 7, 8, 9
local NAMES = { "push", "load", "store", "binary", "neg", "jump", "jumpf", "out", "halt" }

local OPERATORS = {
	["+"] = function(a, b) return a + b end,
	["-"] = function(a, b) return a - b end,
	["*"] = function(a, b) return a * b end,
	["/"] = function(a, b)
		if b == 0 then
			error("division by zero", 0)
		end
		return math.floor(a / b)
	end,
	["%"] = function(a, b) return a % b end,
	["<"] = function(a, b) return a < b and 1 or 0 end,
	[">"] = function(a, b) return a > b and 1 or 0 end,
	["=="] = function(a, b) return a == b and 1 or 0 end,
}
local LEVELS = { { "==", "<", ">" }, { "+", "-" }, { "*", "/", "%" } }

local function tokenize(source)
	local tokens = {}
	local line = 1
	local pos = 1
	while pos <= #source do
		local char = string.sub(source, pos, pos)
		local first, last = string.find(source, "^%d+", pos)
		if char == "\n" then
			line += 1
			last = pos
		elseif char == " " or char == "\t" then
			last = pos
		elseif first ~= nil then
			table.insert(tokens, { kind = "number", text = tonumber(string.sub(source, first, last)), line = line })
		else
			first, last = string.find(source, "^%a%w*", pos)
			if first == nil then
				first, last = string.find(source, "^==", pos)
				if first == nil then
					first, last = pos, pos
				end
			end
			table.insert(tokens, { kind = "word", text = string.sub(source, first, last), line = line })
		end
		pos = last + 1
	end
	table.insert(tokens, { kind = "end", text = "<end>", line = line })
	return tokens
end

local function compile(source, inputs)
	local tokens, index = tokenize(source), 1
	local code, slots, slotCount = {}, {}, 0

	local function emit(op, arg)
		table.insert(code, { op, arg })
		return #code
	end
	local function fail(message)
		error({ kind = "syntax", line = tokens[index].line, message = message }, 0)
	end
	local function accept(text)
		if tokens[index].text == text then
			index += 1
			return true
		end
		return false
	end
	local function expect(text)
		if not accept(text) then
			fail("expected '" .. text .. "' near '" .. tostring(tokens[index].text) .. "'")
		end
	end
	local function slotFor(name, declare)
		if slots[name] == nil then
			if not declare then
				fail("undeclared variable '" .. name .. "'")
			end
			slotCount += 1
			slots[name] = slotCount
		end
		return slots[name]
	end

	local expression
	local function primary()
		local token = tokens[index]
		index += 1
		if token.kind == "number" then
			emit(PUSH, token.text)
		elseif token.text == "(" then
			expression(1)
			expect(")")
		elseif token.text == "-" then
			primary()
			emit(NEG)
		elseif token.kind == "word" and string.find(token.text, "^%a") then
			emit(LOAD, slotFor(token.text, false))
		else
			index -= 1
			fail("unexpected '" .. tostring(token.text) .. "'")
		end
	end
	expression = function(level)
		if level > #LEVELS then
			primary()
			return
		end
		expression(level + 1)
		local matched = true
		while matched do
			matched = false
			for _, op in ipairs(LEVELS[level]) do
				if accept(op) then
					expression(level + 1)
					emit(BINARY, op)
					matched = true
					break
				end
			end
		end
	end

	local block
	local function statement()
		local token = tokens[index]
		if accept("let") or (token.kind == "word" and tokens[index + 1].text == "=") then
			local name = tokens[index].text
			index += 1
			expect("=")
			expression(1)
			emit(STORE, slotFor(name, token.text == "let"))
		elseif accept("out") then
			expression(1)
			emit(OUT)
		elseif accept("while") then
			local top = #code + 1
			expression(1)
			expect("do")
			local exit = emit(JUMP_FALSE, 0)
			block()
			expect("end")
			emit(JUMP, top)
			code[exit][2] = #code + 1
		elseif accept("if") then
			expression(1)
			expect("then")
			local skip = emit(JUMP_FALSE, 0)
			block()
			if accept("else") then
				local over = emit(JUMP, 0)
				code[skip][2] = #code + 1
				block()
				code[over][2] = #code + 1
			else
				code[skip][2] = #code + 1
			end
			expect("end")
		else
			fail("unexpected '" .. tostring(token.text) .. "'")
		end
	end
	block = function()
		while tokens[index].kind ~= "end" and tokens[index].text ~= "end" and tokens[index].text ~= "else" do
			statement()
		end
	end

	for name, value in pairs(inputs) do
		emit(PUSH, value)
		emit(STORE, slotFor(name, true))
	end
	block()
	if tokens[index].kind ~= "end" then
		fail("trailing '" .. tostring(tokens[index].text) .. "'")
	end
	emit(HALT)
	return code, slotCount
end

local function disassemble(code, first, last)
	local lines = {}
	for pc = first, math.min(last, #code) do
		local op, arg = code[pc][1], code[pc][2]
		table.insert(lines, string.format("%3d %-6s %s", pc, NAMES[op], arg == nil and "" or tostring(arg)))
	end
	return table.concat(lines, "\n")
end

local function execute(code, limit)
	local stack, sp, memory, output = {}, 0, {}, {}
	local trace, pc, steps = {}, 1, 0
	local ok, problem = pcall(function()
		repeat
			local op, arg = code[pc][1], code[pc][2]
			steps += 1
			trace[(steps - 1) % 4 + 1] = pc
			if steps > limit then
				error({ kind = "step limit", line = 0, message = "more than " .. limit .. " steps" }, 0)
			end
			pc += 1
			if op == PUSH then
				sp += 1
				stack[sp] = arg
			elseif op == LOAD then
				sp += 1
				stack[sp] = memory[arg]
			elseif op == STORE then
				memory[arg], sp = stack[sp], sp - 1
			elseif op == BINARY then
				stack[sp - 1] = OPERATORS[arg](stack[sp - 1], stack[sp])
				sp -= 1
			elseif op == NEG then
				stack[sp] = -stack[sp]
			elseif op == JUMP then
				pc = arg
			elseif op == JUMP_FALSE then
				if stack[sp] == 0 then
					pc = arg
				end
				sp -= 1
			elseif op == OUT then
				table.insert(output, tostring(stack[sp]))
				sp -= 1
			end
		until op == HALT
	end)
	local recent = {}
	for count = steps, math.max(1, steps - 3), -1 do
		table.insert(recent, tostring(trace[(count - 1) % 4 + 1]))
	end
	return ok, problem, output, steps, table.concat(recent, "<")
end

local PROGRAMS = {
	{ "fibonacci", 2000, "let a = 0\nlet b = 1\nlet i = 0\nwhile i < n + 5 do\n let t = a + b\n a = b\n b = t\n i = i + 1\nend\nout a" },
	{ "gcd", 2000, "let x = 84 * n\nlet y = 36 + n\nwhile y > 0 do\n let r = x % y\n x = y\n y = r\nend\nout x\nout 84 * n * (36 + n) / x" },
	{ "collatz", 2000, "let c = 6 + n * 3\nlet s = 0\nwhile c > 1 do\n if c % 2 == 0 then c = c / 2 else c = 3 * c + 1 end\n s = s + 1\nend\nout s" },
	{ "primes", 4000, "let p = 2\nwhile p < 12 + n * 4 do\n let d = 2\n let q = 1\n while d * d < p + 1 do\n  if p % d == 0 then q = 0 end\n  d = d + 1\n end\n if q == 1 then out p end\n p = p + 1\nend" },
	{ "divide", 100, "let z = n - n\nout 7 - -n\nout 10 / z" },
	{ "spin", 250, "let k = 0\nwhile 1 do k = k + 1 end" },
	{ "broken", 100, "let v = (n + 2\nout v" },
	{ "unknown", 100, "out w + 1" },
}

return function(n)
	local lines = {}
	for _, entry in ipairs(PROGRAMS) do
		local name, limit, source = entry[1], entry[2], entry[3]
		local compiled, code, slotCount = pcall(compile, source, { n = n })
		if not compiled then
			table.insert(lines, string.format("%-9s compile error (%s) line %d: %s", name, code.kind, code.line, code.message))
			continue
		end
		local ok, problem, output, steps, recent = execute(code, limit + n * 10)
		local status = "ok"
		if not ok and type(problem) == "table" then
			status = problem.kind .. ": " .. problem.message
		elseif not ok then
			status = "error: " .. problem
		end
		table.insert(lines, string.format("%-9s %2d ops %d slots %4d steps [%s] %s, trace %s",
			name, #code, slotCount, steps, table.concat(output, " "), status, recent))
		if name == "collatz" then
			table.insert(lines, disassemble(code, 5 + n, 9 + n))
		end
	end
	return table.concat(lines, "\n")
end

end)()

local bench_calc = (function()

local function lex(source)
	local tokens, pos = {}, 1
	while pos <= #source do
		local byte = string.byte(source, pos)
		if byte == 32 or byte == 9 then
			pos += 1
			continue
		end
		local first, last = string.find(source, "^%d+%.?%d*", pos)
		if first ~= nil then
			table.insert(tokens, { kind = "number", value = tonumber(string.sub(source, first, last)), pos = pos })
		else
			first, last = string.find(source, "^[%a_][%w_]*", pos)
			if first ~= nil then
				table.insert(tokens, { kind = "name", value = string.sub(source, first, last), pos = pos })
			else
				local char = string.char(byte)
				if string.find("+-*/%^(),=<>", char, 1, true) == nil then
					error({ code = "bad_char", pos = pos, text = char }, 0)
				end
				last = pos
				table.insert(tokens, { kind = "op", value = char, pos = pos })
			end
		end
		pos = last + 1
	end
	table.insert(tokens, { kind = "eof", value = "<eof>", pos = #source + 1 })
	return tokens
end

local INFIX = { ["="] = { 2, 1 }, ["<"] = { 3, 4 }, [">"] = { 3, 4 }, ["+"] = { 5, 6 }, ["-"] = { 5, 6 },
	["*"] = { 7, 8 }, ["/"] = { 7, 8 }, ["%"] = { 7, 8 }, ["^"] = { 12, 11 } }
local PREFIX_POWER = 9

local Parser = {}
Parser.__index = Parser

function Parser.new(tokens)
	return setmetatable({ tokens = tokens, index = 1 }, Parser)
end

function Parser:peek()
	return self.tokens[self.index]
end

function Parser:advance()
	local token = self.tokens[self.index]
	self.index += 1
	return token
end

function Parser:arguments()
	local args = {}
	if self:peek().value == ")" then
		self:advance()
		return args
	end
	repeat
		table.insert(args, self:expression(0))
		local token = self:advance()
		if token.value ~= "," and token.value ~= ")" then
			error({ code = "expected", pos = token.pos, text = ", or )" }, 0)
		end
	until token.value == ")"
	return args
end

function Parser:primary()
	local token = self:advance()
	if token.kind == "number" then
		return { tag = "num", value = token.value }
	elseif token.kind == "name" then
		if self:peek().value == "(" then
			self:advance()
			return { tag = "call", name = token.value, args = self:arguments(), pos = token.pos }
		end
		return { tag = "var", name = token.value, pos = token.pos }
	elseif token.value == "-" then
		return { tag = "neg", operand = self:expression(PREFIX_POWER) }
	elseif token.value == "(" then
		local inner = self:expression(0)
		local closing = self:advance()
		if closing.value ~= ")" then
			error({ code = "expected", pos = closing.pos, text = ")" }, 0)
		end
		return inner
	end
	error({ code = "unexpected", pos = token.pos, text = tostring(token.value) }, 0)
end

function Parser:expression(minPower)
	local left = self:primary()
	while true do
		local token = self:peek()
		local powers = INFIX[token.value]
		if token.kind ~= "op" or powers == nil or powers[1] < minPower then
			break
		end
		self:advance()
		local right = self:expression(powers[2])
		if token.value == "=" then
			if left.tag ~= "var" then
				error({ code = "assign_target", pos = token.pos, text = left.tag }, 0)
			end
			left = { tag = "assign", name = left.name, value = right }
		else
			left = { tag = "binary", op = token.value, left = left, right = right }
		end
	end
	return left
end

local builtins = {}

function builtins.max(...)
	local count = select("#", ...)
	if count == 0 then
		error("max needs at least one argument", 0)
	end
	local best = ...
	for index = 2, count do
		local value = select(index, ...)
		if value > best then
			best = value
		end
	end
	return best
end

function builtins.avg(...)
	local count = select("#", ...)
	local total = 0
	for _, value in ipairs({ ... }) do
		total += value
	end
	if count == 0 then
		error({ code = "arity", pos = 0, text = "avg needs arguments" }, 0)
	end
	return total / count
end

local function makeMachine()
	local variables = {}
	local operations = 0

	local function compile(node)
		local tag = node.tag
		if tag == "num" then
			local value = node.value
			return function() return value end
		elseif tag == "var" then
			return function()
				local value = variables[node.name]
				if value == nil then
					error({ code = "undefined", pos = node.pos, text = node.name }, 0)
				end
				return value
			end
		elseif tag == "assign" then
			local name, valueOf = node.name, compile(node.value)
			return function()
				local value = valueOf()
				variables[name] = value
				return value
			end
		elseif tag == "neg" then
			local operandOf = compile(node.operand)
			return function() return -operandOf() end
		elseif tag == "call" then
			local fn = builtins[node.name]
			if fn == nil then
				error({ code = "unknown_function", pos = node.pos, text = node.name }, 0)
			end
			local argumentsOf = {}
			for index, argument in ipairs(node.args) do
				argumentsOf[index] = compile(argument)
			end
			return function()
				local values = {}
				for index, argumentOf in ipairs(argumentsOf) do
					values[index] = argumentOf()
				end
				return fn(table.unpack(values, 1, #argumentsOf))
			end
		end
		local op, leftOf, rightOf = node.op, compile(node.left), compile(node.right)
		return function()
			local a, b = leftOf(), rightOf()
			operations += 1
			if op == "+" then
				return a + b
			elseif op == "-" then
				return a - b
			elseif op == "*" then
				return a * b
			elseif op == "/" or op == "%" then
				if b == 0 then
					error("division by zero in '" .. op .. "'", 0)
				end
				return op == "/" and a / b or a % b
			elseif op == "^" then
				return a ^ b
			elseif op == "<" then
				return a < b and 1 or 0
			end
			return a > b and 1 or 0
		end
	end

	local function run(source)
		local parser = Parser.new(lex(source))
		local tree = parser:expression(0)
		local rest = parser:peek()
		if rest.kind ~= "eof" then
			error({ code = "trailing", pos = rest.pos, text = tostring(rest.value) }, 0)
		end
		return compile(tree)()
	end

	return run, function() return operations end, variables
end

local function formatNumber(value)
	if value == math.floor(value) and math.abs(value) < 1e12 then
		return string.format("%d", value)
	end
	return string.format("%.6g", value)
end

local OPERATORS = { "+", "-", "*", "/", "%", "^", "<" }
local NAMES = { "x", "y", "z", "w" }

local function randomExpression(state, depth)
	state.seed = state.seed * 16807 % 2147483647
	local roll = state.seed % 10
	if depth <= 0 or roll < 3 then
		if roll == 1 then
			return tostring(state.seed % 20)
		end
		return NAMES[state.seed % #NAMES + 1]
	elseif roll == 3 then
		return "-" .. randomExpression(state, depth - 1)
	elseif roll == 4 then
		return "max(" .. randomExpression(state, depth - 1) .. ", " .. randomExpression(state, depth - 1) .. ")"
	end
	local op = OPERATORS[state.seed % #OPERATORS + 1]
	if op == "^" then
		return "(" .. randomExpression(state, depth - 1) .. ")^" .. tostring(state.seed % 3)
	end
	return "(" .. randomExpression(state, depth - 1) .. " " .. op .. " " .. randomExpression(state, depth - 1) .. ")"
end

local SCRIPT = {
	"x = 4", "y = x * 2 + 1", "z = (x + y) * (y - x) / 3", "w = n % 4 + 0.5",
	"2 ^ 3 ^ 2 - -2 ^ 2", "10 % 4 + 7 % -3", "max(x, y, z, 2 ^ 5) > avg(1, 2, 3, 4, n)",
	"(x * y + n) ^ 0.5", "1 / (n - n)", "x = y = n * 3", "q + 1", "3 $ 4", "(1 + 2",
	"avg() + 1", "max()", "pow(2, 3)",
}

return function(n)
	local run, operationCount, variables = makeMachine()
	variables.n = n
	local lines, failures = {}, 0
	local function attempt(source)
		local ok, result = pcall(run, source)
		if ok then
			table.insert(lines, string.format("%-26s = %s", source, formatNumber(result)))
		elseif type(result) == "table" then
			failures += 1
			table.insert(lines, string.format("%-26s ! %s at %d (%s)", source, result.code, result.pos, result.text))
		else
			failures += 1
			table.insert(lines, string.format("%-26s ! %s", source, result))
		end
	end
	for _, source in ipairs(SCRIPT) do
		attempt(source)
	end
	local state = { seed = n * 7919 + 17 }
	for _ = 1, 4 + n do
		attempt(randomExpression(state, 3))
	end
	local bindings = {}
	for name, value in pairs(variables) do
		table.insert(bindings, name .. "=" .. formatNumber(value))
	end
	table.sort(bindings, function(a, b)
		return a < b
	end)
	table.insert(lines, string.format("ok=%d failed=%d operations=%d", #lines - failures, failures, operationCount()))
	table.insert(lines, table.concat(bindings, " "))
	return table.concat(lines, "\n")
end

end)()

local bench_json = (function()

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

end)()

local bench_life = (function()

local Grid = {}
Grid.__index = Grid

function Grid.new(width, height)
	local cells = {}
	for index = 1, width * height do
		cells[index] = false
	end
	return setmetatable({ width = width, height = height, cells = cells }, Grid)
end

function Grid:index(x, y)
	return ((y - 1) % self.height) * self.width + (x - 1) % self.width + 1
end

function Grid:get(x, y)
	return self.cells[self:index(x, y)]
end

function Grid:set(x, y, alive)
	self.cells[self:index(x, y)] = alive
end

Grid.__eq = function(a, b)
	if a.width ~= b.width or a.height ~= b.height then
		return false
	end
	for index, alive in ipairs(a.cells) do
		if b.cells[index] ~= alive then
			return false
		end
	end
	return true
end

function Grid:neighbours(x, y)
	local count = 0
	for dy = -1, 1 do
		for dx = -1, 1 do
			if (dx ~= 0 or dy ~= 0) and self:get(x + dx, y + dy) then
				count += 1
			end
		end
	end
	return count
end

function Grid:step(rule)
	local nextGrid = Grid.new(self.width, self.height)
	local births, deaths = 0, 0
	for y = 1, self.height do
		for x = 1, self.width do
			local alive, count = self:get(x, y), self:neighbours(x, y)
			local lives = false
			if alive then
				lives = rule.survive[count] == true
				if not lives then
					deaths += 1
				end
			elseif rule.born[count] then
				lives = true
				births += 1
			end
			nextGrid:set(x, y, lives)
		end
	end
	return nextGrid, births, deaths
end

function Grid:population()
	local count = 0
	for _, alive in ipairs(self.cells) do
		if alive then
			count += 1
		end
	end
	return count
end

function Grid:render()
	local rows = {}
	for y = 1, self.height do
		local row = {}
		for x = 1, self.width do
			row[x] = self:get(x, y) and "#" or "."
		end
		rows[y] = table.concat(row)
	end
	return table.concat(rows, "\n")
end

local function rowHasLife(grid, y)
	for x = 1, grid.width do
		if grid:get(x, y) then
			return true
		end
	end
	return false
end

local function columnHasLife(grid, x)
	for y = 1, grid.height do
		if grid:get(x, y) then
			return true
		end
	end
	return false
end

function Grid:boundingBox()
	local top, bottom, left, right = nil, nil, nil, nil
	for y = 1, self.height do
		if rowHasLife(self, y) then
			top = y
			break
		end
	end
	if top == nil then
		return nil
	end
	for y = self.height, top, -1 do
		if rowHasLife(self, y) then
			bottom = y
			break
		end
	end
	for x = 1, self.width do
		if columnHasLife(self, x) then
			left = x
			break
		end
	end
	for x = self.width, left, -1 do
		if columnHasLife(self, x) then
			right = x
			break
		end
	end
	return top, bottom, left, right
end

local function parseRule(text)
	local born, survive = string.match(text, "^B(%d*)/S(%d*)$")
	if born == nil then
		error({ rule = text, reason = "expected B<digits>/S<digits>" }, 0)
	end
	local rule = { name = text, born = {}, survive = {} }
	for index = 1, #born do
		rule.born[string.byte(born, index) - 48] = true
	end
	for digit in string.gmatch(survive, "%d") do
		rule.survive[tonumber(digit)] = true
	end
	return rule
end

local PATTERNS = {
	glider = ".#.|..#|###",
	blinker = "###",
	toad = ".###|###.",
	rpentomino = ".##|##.|.#.",
	block = "##|##",
	domino = "##",
}

local function stamp(grid, pattern, originX, originY)
	local y = originY
	local placed = 0
	for row in string.gmatch(PATTERNS[pattern] .. "|", "([^|]*)|") do
		for x = 1, #row do
			if string.sub(row, x, x) == "#" then
				grid:set(originX + x - 1, y, true)
				placed += 1
			end
		end
		y += 1
	end
	return placed
end

local SCENARIOS = {
	{ "B3/S23", { "blinker" } },
	{ "B36/S23", { "rpentomino" } },
	{ "B3/S23", { "toad", "block", "glider" } },
	{ "B2/S", { "blinker" } },
	{ "B3/S12345", { "rpentomino", "block" } },
	{ "B3S23", { "glider" } },
	{ "B3/S23", { "domino", "glider" } },
	{ "B3/S23", { "domino" } },
}

local function run(n, scenario)
	local ok, rule = pcall(parseRule, scenario[1])
	if not ok then
		return { string.format("rule %s rejected: %s", rule.rule, rule.reason) }
	end
	local grid = Grid.new(10, 8)
	local placed = 0
	for index, pattern in ipairs(scenario[2]) do
		placed += stamp(grid, pattern, 1 + (index * 3 + n) % 8, 1 + (index * 2 + n) % 6)
	end
	local lines = { string.format("rule %s, %d cells placed", rule.name, placed) }
	local history, seen = { grid:population() }, { [grid:render()] = 0 }
	local totalBirths, totalDeaths = 0, 0
	for generation = 1, n + 3 do
		local nextGrid, births, deaths = grid:step(rule)
		totalBirths += births
		totalDeaths += deaths
		if nextGrid == grid then
			table.insert(lines, string.format("still life after %d generations", generation - 1))
			break
		end
		grid = nextGrid
		table.insert(history, grid:population())
		local picture = grid:render()
		if seen[picture] ~= nil then
			table.insert(lines, string.format("cycle of period %d at generation %d", generation - seen[picture], generation))
			break
		end
		seen[picture] = generation
	end
	table.insert(lines, string.format("population %s; births %d deaths %d", table.concat(history, " "), totalBirths, totalDeaths))
	local top, bottom, left, right = grid:boundingBox()
	if top == nil then
		table.insert(lines, "extinct")
	else
		table.insert(lines, string.format("box rows %d-%d columns %d-%d", top, bottom, left, right))
		table.insert(lines, grid:render())
	end
	return lines
end

return function(n)
	local output = {}
	for _, offset in ipairs({ 0, 3 }) do
		local scenario = SCENARIOS[(n + offset - 1) % #SCENARIOS + 1]
		for _, line in ipairs(run(n, scenario)) do
			table.insert(output, line)
		end
	end
	return table.concat(output, "\n")
end

end)()

return function(n)
  local output = {
    "stackvm\n" .. bench_stackvm(n),
    "calc\n" .. bench_calc(n),
    "json\n" .. bench_json(n),
    "life\n" .. bench_life(n),
  }
  return table.concat(output, "\n")
end
