#!/usr/bin/perl -w
use strict;

use Getopt::Long;
use Pod::Usage;

Getopt::Long::Configure("bundling"); #allow -optVALUE whithout spaces

# debug
my $debug = 0;

# avoid verbose output
my $quiet = 0;

my $help = 0;

my $filename;

# signal handling
sub catch {
    my $signame = shift;
    print "Caught SIG${signame}";
}
$SIG{USR1} = \&catch;

my $usage = <<EOT;
cnf2smv.pl - (c) Marco Pensallorto 2011.
Converts cnf files into SMV models.

usage:
    cnf2mv <filename>

    -q    be quiet.

EOT

    GetOptions
    (
    "q"  => \$quiet,

    "d"  => \$debug,

    # "l"  => \$tabular,

    # "t=s" =>
    # sub {
    #     my $tmp = $_[1];
    #     die "$tmp is not valid numeric number" unless (0 <= $tmp);

    #     $timeout = $tmp;
    #     print "setting timeout: $timeout" ."\n" unless $quiet;
    # },

    # "m=s" =>
    # sub {
    #     my $tmp = $_[1];
    #     die "$tmp is not valid numeric number" unless (0 <= $tmp);

    #     $memout = $tmp;
    #     print "setting memout: $memout" ."\n" unless $quiet;
    # },

    # "o=s" =>
    # sub {
    #     my $tmp = $_[1];

    #     $output_file = $tmp;
    #     print "using output: $output_file" ."\n" unless $quiet;
    # },

    # "j=s" =>
    # sub {
    #      my $tmp = $_[1];
    #      die "$tmp is not valid numeric number" unless (0 <= $tmp);

    #     $cores = $tmp;
    #     print "setting number of cores: $cores" ."\n" unless $quiet;
    # },

    "h" => \$help
    ) or die $usage;

# usage message
pod2usage({-exitval => 1, -verbose => 1, -output => \*STDOUT, -message => $usage}) if @ARGV < 1 || $help;

sub cnf2smvlit($)
{
    my $lit = int(shift);

    if ($lit < 0) {
        return sprintf("x%d", - $lit -1); ## convert
    }
    elsif ($lit > 0) {
        return sprintf("x%d", $lit -1); ## convert
    }
    elsif ($lit == 0) {
        return ();
    }
}

sub process($)
{
    my $input = shift;
    open (CNF, "$input");

    my $output = "$input.smv";
    open (SMV, ">$output");
    print "-- creating output file $output\n" unless $quiet;

    # TODO: header
    print SMV "MODULE main\n\n";

    my $nvars;
    my $nclauses;
    my $cclauses = 0; # count clauses

    while (my $line = <CNF>) {
        if ($line =~ /^c.*/) { next; } # skip comments
        if ($line =~ /^p cnf (\d+)\s+(\d+)/) {
            $nvars = $1;
            print "-- $nvars boolean variables\n" unless $quiet;

            $nclauses = $2;
            print "-- $nclauses clauses\n" unless $quiet;

            print SMV "-- $nvars boolean variables\n";
            for (my $i = 0; $i < $nvars; $i ++) {
                print SMV "VAR x$i: boolean;\n";
            }
            print SMV "\n";

            next;
        }

        print SMV "DEFINE c$cclauses := ";
        my @smv_lits = map { cnf2smvlit($_) } split (/ /, $line);
        print SMV join (" | ", @smv_lits ) . ";\n";
        $cclauses ++;
    }

    print SMV "-- conjuction of all clauses\n";
    print SMV "DEFINE phi := ";
    print SMV join (" & ", map { "c$_" } 0..$nclauses ) . ";\n";

}

$filename = $ARGV[0]; die "$filename is not a file." unless -f $filename;
print "input file: $filename" . "\n" unless $quiet;

process($filename);

exit 0;
