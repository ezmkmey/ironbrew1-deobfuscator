
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
