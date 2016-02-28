#!/usr/bin/perl   
#!/usr/local/bin/perl 
print "hello";
print "\n";
open(out, ">res/_res.txt") or die $!;
print out ("compile error\n");
