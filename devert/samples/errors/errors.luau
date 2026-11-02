return function(n)
	local message = "Tamper Detected!"
	local function conditional(x)
		if x % 2 == 0 then error("expected application error", 0) end
		return x * 3
	end
	local function sameMessage(x)
		if x % 3 == 0 then error(message, 0) end
		return x + 7
	end
	local f = conditional
	if n > 3 then f = sameMessage end
	local ok, value = pcall(f, n)
	local ok2, value2 = pcall(sameMessage, n)
	return tostring(ok) .. ":" .. tostring(value) .. ":" .. tostring(ok2) .. ":" .. tostring(value2) .. ":" .. message
end
