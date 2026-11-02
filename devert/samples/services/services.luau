return function(n)
    local x=game:GetService("ReplicatedStorage")
    local y=x:WaitForChild("RemoteEvent")
    local z=Instance.new("Part")
    local a,b=1,1.25
    return x.Name..":"..y.Name..":"..z.ClassName..":"..tostring(n+a+b)
end
