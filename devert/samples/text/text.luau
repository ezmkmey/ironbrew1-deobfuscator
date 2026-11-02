
local PASSAGES = {
	"The quick brown fox jumps over the lazy dog. The dog sleeps; the fox runs on!",
	"Pack my box with five dozen liquor jugs, then pack the box again and again.",
	"How vexingly quick daft zebras jump: zebras jump, foxes run, dogs sleep soundly.",
	"Sphinx of black quartz, judge my vow; the vow is old and the quartz is black.",
	"Bright vixens jump; dozy fowl quack. The fowl sleep and the vixens run away.",
}
local KEYS = { "lemon", "quartz", "abc", "zebra", "key" }
local ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

local function wordFrequencies(text)
	local counts, order, total = {}, {}, 0
	for word in string.gmatch(string.lower(text), "%a+") do
		total += 1
		if #word < 3 then
			continue
		end
		if counts[word] == nil then
			counts[word] = 0
			table.insert(order, word)
		end
		counts[word] += 1
	end
	table.sort(order, function(a, b)
		if counts[a] ~= counts[b] then
			return counts[a] > counts[b]
		end
		return a < b
	end)
	return counts, order, total
end

local function shiftByte(byte, shift)
	if byte >= 65 and byte <= 90 then
		return (byte - 65 + shift) % 26 + 65
	elseif byte >= 97 and byte <= 122 then
		return (byte - 97 + shift) % 26 + 97
	end
	return byte
end

local function caesar(text, shift)
	local out = {}
	for index = 1, #text do
		out[index] = string.char(shiftByte(string.byte(text, index), shift))
	end
	return table.concat(out)
end

local function vigenere(text, key, direction)
	local out, keyIndex = {}, 0
	for index = 1, #text do
		local byte = string.byte(text, index)
		if (byte >= 65 and byte <= 90) or (byte >= 97 and byte <= 122) then
			local shift = string.byte(key, keyIndex % #key + 1) - 97
			byte = shiftByte(byte, direction * shift)
			keyIndex += 1
		end
		out[index] = string.char(byte)
	end
	return table.concat(out)
end

local function runLengthEncode(text)
	local parts, index = {}, 1
	while index <= #text do
		local char = string.sub(text, index, index)
		local runEnd = index
		while runEnd < #text and string.sub(text, runEnd + 1, runEnd + 1) == char do
			runEnd += 1
		end
		local count = runEnd - index + 1
		if count > 1 then
			table.insert(parts, count .. char)
		else
			table.insert(parts, char)
		end
		index = runEnd + 1
	end
	return table.concat(parts)
end

local function runLengthDecode(text)
	return (string.gsub(text, "(%d*)(%D)", function(count, char)
		return string.rep(char, tonumber(count) or 1)
	end))
end

local function base64Encode(data)
	local out = {}
	for index = 1, #data, 3 do
		local a, b, c = string.byte(data, index, index + 2)
		local triple = a * 65536 + (b or 0) * 256 + (c or 0)
		local chars = {}
		for slot = 4, 1, -1 do
			local sextet = triple % 64
			triple = math.floor(triple / 64)
			chars[slot] = string.sub(ALPHABET, sextet + 1, sextet + 1)
		end
		if c == nil then
			chars[4] = "="
			if b == nil then
				chars[3] = "="
			end
		end
		table.insert(out, table.concat(chars))
	end
	return table.concat(out)
end

local function base64Decode(text)
	local lookup = {}
	for index = 1, #ALPHABET do
		lookup[string.sub(ALPHABET, index, index)] = index - 1
	end
	local out = {}
	for index = 1, #text, 4 do
		local triple, padding = 0, 0
		for offset = index, index + 3 do
			local char = string.sub(text, offset, offset)
			local value = lookup[char]
			if char == "=" then
				padding += 1
				value = 0
			elseif value == nil then
				error({ position = offset, char = char }, 0)
			end
			triple = triple * 64 + value
		end
		local bytes = { math.floor(triple / 65536), math.floor(triple / 256) % 256, triple % 256 }
		table.insert(out, string.char(table.unpack(bytes, 1, 3 - padding)))
	end
	return table.concat(out)
end

local function makePipeline(...)
	local stages = { ... }
	local count = select("#", ...)
	return function(text)
		local trace = {}
		for index = 1, count do
			text = stages[index](text)
			trace[index] = #text
		end
		return text, table.concat(trace, ">")
	end
end

local function countOccurrences(text, needle)
	local count, start = 0, 1
	while true do
		local first, last = string.find(text, needle, start, true)
		if first == nil then
			break
		end
		count += 1
		start = last + 1
	end
	return count
end

local function preview(text, width)
	if #text <= width then
		return text
	end
	return string.sub(text, 1, width - 3) .. "..."
end

return function(n)
	local text = PASSAGES[(n - 1) % #PASSAGES + 1] .. " " .. PASSAGES[n % #PASSAGES + 1]
	local key = KEYS[n % #KEYS + 1]
	local lines = {}

	local counts, order, total = wordFrequencies(text)
	local top = {}
	for rank = 1, math.min(6, #order) do
		top[rank] = string.format("%s:%d", order[rank], counts[order[rank]])
	end
	table.insert(lines, string.format("words %d, distinct long words %d, top %s", total, #order, table.concat(top, " ")))
	table.insert(lines, string.format("'the' occurs %d times, 'jump' %d times", countOccurrences(string.lower(text), "the"), countOccurrences(text, "jump")))

	local shifted = caesar(text, n * 3)
	table.insert(lines, "caesar " .. preview(shifted, 64))
	table.insert(lines, "caesar round trip " .. tostring(caesar(shifted, -n * 3) == text))
	local secret = vigenere(text, key, 1)
	table.insert(lines, "vigenere(" .. key .. ") " .. preview(secret, 64))
	table.insert(lines, "vigenere round trip " .. tostring(vigenere(secret, key, -1) == text))

	local initials = {}
	for rank = 1, math.min(5, #order) do
		local word = order[rank]
		table.insert(initials, string.rep(string.sub(word, 1, 1), counts[word] + (rank + n) % 4))
	end
	local runs = table.concat(initials) .. string.rep("z", n)
	local packed = runLengthEncode(runs)
	table.insert(lines, string.format("rle %s -> %s (%s)", runs, packed, tostring(runLengthDecode(packed) == runs)))

	local bytes = {}
	for index = 1, 8 + n do
		bytes[index] = string.char((index * 37 + n * 11) % 256)
	end
	local binary = table.concat(bytes)
	for _, sample in ipairs({ string.sub(text, 1, n + 4), binary }) do
		local encoded = base64Encode(sample)
		table.insert(lines, string.format("base64 %s (%d -> %d) %s", encoded, #sample, #encoded, tostring(base64Decode(encoded) == sample)))
	end
	local ok, problem = pcall(base64Decode, "QUJD*A==")
	table.insert(lines, ok and "decoded bad base64" or string.format("bad base64 at %d: '%s'", problem.position, problem.char))

	local titled = string.gsub(string.lower(PASSAGES[n % #PASSAGES + 1]), "(%a)(%w*)", function(first, rest)
		return string.upper(first) .. rest
	end)
	local pipeline = makePipeline(string.lower, function(s)
		return (string.gsub(s, "[^%a ]", ""))
	end, function(s)
		return caesar(s, n)
	end, base64Encode)
	local result, trace = pipeline(titled)
	table.insert(lines, "title " .. preview(titled, 60))
	table.insert(lines, string.format("pipeline %s %s", trace, preview(result, 48)))
	return table.concat(lines, "\n")
end
