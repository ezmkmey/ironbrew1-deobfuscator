return function(n)
	local sum = 1
	local t = { offset = n, label = "proxy" }
	local t2 = { 3, 5, 7 }
	local ofs = t.offset

	for i = 1, n do
		sum += i * ofs
	end

	return ("proxy" .. ":" .. tostring(sum)) .. ":" .. tostring(t2[n % 3 + 1])
end
