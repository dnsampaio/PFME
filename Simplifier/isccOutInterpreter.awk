BEGIN{
	T=1;
}

/card====/{ #Testing affine part cardinality
	print "card";
	s=1;
	next;
}

/lb====/{ #Testing a polynomial lb
	print "lb";
	s=2;
	next;
}

/ub====/{ #Testing a polynomial ub
	print "ub";
	s=3;
	next;
}

!s{ #Not testing anything
	next;
}

/{\s*}/{ #If any of the tests has "{  }", then the system is FALSE
	T=0;
	exit 0;
}

(s==2)&&(/{\s*[1-9][0-9]*\s*}/|| /{\s*min\s*\(\s*[1-9][0-9]*\s*\)\s:*/){ #If the lb is a numeric > 0 ==> { [min(] [::NUMBER::] [)] }; then the system is FALSE
	T=0;
	exit 0;
}

(s==3)&&(/\s*-[1-9][0-9]*\s*}/ || /{\s*max\s*\(\s*-[1-9][0-9]*\s*\)\s:*/){ #If the ub is a numeric < 0 ==> { [max(] -[::NUMBER::] [)] }; then the system is FALSE
	T=0;
	exit 0;
}

END{ #The system might not be FALSE :(
	if ( T == 1 )
		print "MIGHT NOT BE FALSE"
	else
		print "FALSE"

	exit T;
}

