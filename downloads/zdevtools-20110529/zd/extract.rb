#!/usr/bin/ruby -w

require "readbytes"
require "fileutils"

EXT = {
  "JPEG" => ".jpg",
  "PNG " => ".png",
  "MOD " => ".mod",
  "AIFF" => ".aiff",
  "GLUL" => ".ulx",
  "ZCOD" => ".z8",
  "IFmd" => ".xml",
  "OGGV" => ".ogg",
}

ARGV.each do |blorb|
  File.open(blorb) do |f|
    raise "Not a Blorb file" if f.readbytes(4) != "FORM"
    f.seek 8, IO::SEEK_SET
    raise "Not a Blorb file" if f.readbytes(4) != "IFRS" || f.readbytes(4) != "RIdx"

    size = f.readbytes(4).unpack("N1").first
    f.seek size, IO::SEEK_CUR

    counters = Hash.new 0

    FileUtils.mkdir_p "extracted/#{File.basename blorb}"
    Dir.chdir("extracted/#{File.basename blorb}") do
      begin
        while type = f.readbytes(4)
          size = f.readbytes(4).unpack("N1").first
          chunk = f.readbytes(size)

          if type == "FORM" && chunk[0, 4] == "AIFF" # ARGH, special case
            chunk = "FORM" + [size].pack("N1") + chunk
            type = "AIFF"
          end

          if chunk
            puts type
            counters[type] += 1

            File.open(sprintf("#{type.gsub %r{\s+}, ""}%03d#{EXT[type]}", counters[type]), "w") { |e| e.write chunk }
          end

          f.seek 1, IO::SEEK_CUR if size % 2 != 0
        end
      rescue EOFError
      end
    end
  end
end
