return function(n)
	local function fn(n2)
		if n2 % 3 == 0 then
			error("Tamper Detected!", 0)
		end

		return n2 + 7
	end

	local function fn2(n2)
		if n2 % 2 == 0 then
			error("expected application error", 0)
		end

		return n2 * 3
	end

	if n > 3 then
		fn2 = fn
	end

	local ok, res = pcall(fn2, n)
	local ok2, res2 = pcall(fn, n)
	return tostring(ok) .. ":" .. tostring(res) .. ":" .. tostring(ok2)
		.. ":" .. tostring(res2) .. ":" .. "Tamper Detected!"
end
