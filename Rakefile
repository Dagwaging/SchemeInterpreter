task :scheme_test, :paths do |t, args|
  args.paths.each do |file|
    file_number = file[/(\d+)\.ss/, 1].rjust(2, '0') 
    file_test = "A#{file_number}-test-code.ss"

    if !File.exists?(file_test)
      `curl http://www.rose-hulman.edu/class/csse/csse304/201530/Homework/Assignment_#{file_number}/#{file_test} -o #{file_test}`
    end

    print `echo "(r)" | petite #{file} #{file_test} -q 2>&1`
  end
end
