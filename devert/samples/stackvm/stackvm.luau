
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
