#!/usr/bin/ruby -w

# Feed the output of "infodump -g" into this program.

@state = nil
@vals = []

def add(v)
  begin
    v = "%06x" % Integer("0x#{v}")
    @vals << v unless v == "000000"
  rescue ArgumentError
    # Don't worry if v is not a proper hexadecimal value.
  end
end

$stdin.readlines.select { |l| l != "\n" }.each do |l|
  @state = :action if l["action-routine"]
  @state = :preaction if l["pre-action-routine"]
  @state = nil if l["***"]

  s = l.sub(%r{\s+".*}, "").split

  if @state == :preaction
    add s[1]
    add s[2]
  elsif @state == :action
    add s[1]
  end
end

puts @vals.sort.uniq
