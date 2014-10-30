# Preprocessor.
require 'erb'

# The version of Coq.
version = `coqc -v`.match(/version ([^(]*) \(/)[1]

# Number of generated files.
nb_generated = 0

Dir.glob("*.v.erb") do |file_name|
  renderer = ERB.new(File.read(file_name, encoding: "UTF-8"))
  File.open(file_name[0..-5], "w") do |file|
    file << renderer.result()
  end
  puts file_name
  nb_generated += 1
end

puts "#{nb_generated} .erb file(s)."