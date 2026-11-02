return function(n)
	local total = 1
	local record = { offset = n, label = "proxy" }
	local values = { 3, 5, 7 }
	local offset = record.offset
	for i = 1, n do total = total + i * offset end
	local result = record.label .. ":" .. tostring(total)
	return result .. ":" .. tostring(values[n % 3 + 1])
end
