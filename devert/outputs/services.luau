return function(n)
	local rstr = game:GetService("ReplicatedStorage")
	local evt = rstr:WaitForChild("RemoteEvent")
	local part = Instance.new("Part")
	return rstr.Name .. ":" .. evt.Name .. ":" .. part.ClassName .. ":" .. tostring(n + 1 + 1.25)
end
