return function(n)
	local sum = 3

	local function fn(n2)
		sum += n2
		return sum
	end

	local t = { run = function(n2)
		return fn(n2) * 2
	end }

	local function fn2(n2)
		local run = t.run

		if n2 % 2 == 0 then
			run = function(n3)
				return fn(n3) - 1
			end
		end

		return run(n2)
	end

	local function fn3(n2)
		if n2 == 0 then
			return sum
		end
		return fn2(n2) + fn3(n2 - 1)
	end

	local n2 = fn3(n)

	t.run = function(n3)
		return fn(-n3)
	end

	return tostring(n2) .. ":" .. tostring(t.run(n)) .. ":" .. tostring(sum)
end
