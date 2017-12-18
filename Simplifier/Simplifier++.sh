#set -x
DEBUG=0;
###################  Functions ############################################
#Defines number of Running jobs limit
disable_debug () {
	if [[ "$-" == *x* ]]; then
		DEBUG=0;
		set +x;
	else
  	DEBUG=1;
	fi
}

restore_debug () {
	if [[ ${DEBUG} -eq 0 ]]; then
		set -x;
	fi
}

set_NUM_PROCS () {
	if [ -f cpu_limit ] && [ `cat cpu_limit | wc -l` -eq 1 ]; then
		NUM_PROCS=`cat cpu_limit`;
	fi
}

#Obtains number of Running jobs
njobs() {
#	jobs -l > /dev/null 2> /dev/null;
	jobs -l | grep -c 'Running'
}

#Busy waits until number of Running jobs is < limit
wait_for_limits() {
	disable_debug;
#	set_NUM_PROCS;
	while [[ `njobs` -ge $NUM_PROCS ]]; do
		sleep 0.01;
#		set_NUM_PROCS;
	done
	restore_debug;
}

iscc_test () {
	echo $1  | simplifier2iscc | awk -f ${ISCC_IN_AWKF} | tee $2 | iscc | tee $2 | awk -f ${ISCC_AWKF} >> $2;
	return $?
}

reduce_test () {
	return 1;
}

#Processes a system of constraints
#All our system files hold one system per line
#2 Header lines hold the source (original) file and the line number from where the systems came from
#Arguments:
#        1: Full path file
#        2: Line number of the system
#        3: The system
process_line () {
	local MF REF REF_L LOGF SIMP;
	MF=${SWF}/$BASHPID; #My File ==> file where this process writes to
	echo $1 > ${MF};
	echo $2 >> ${MF};
	REF="$(basename $1)";
	SIMP=${PREFIX}/${REF}.Simplifier;
	LOGF=${LG}/$REF.${2}.$BASHPID
	[ ! -e ${SIMP} ] && \rm ${MF} && exit;

	iscc_test "$3" ${LOGF};
	if [[ $? -eq 0 ]]; then
		echo "[]->[]:false;" >> $MF;
		exit;
	fi

	reduce_test "$3" ${LOGF};
	if [[ $? -eq 0 ]]; then
		echo "[]->[]:false;" >> $MF;
		exit;
	fi

	echo $3 | ${SIMP} >> ${MF} 2>> ${LOGF}
	if [[ 0 -ne $? ]]; then #glpk has some strange asserts, try up to 3x before giving up
		echo $3  | ${SIMP} >> ${MF} 2>> ${LOGF}
		if [[ 0 -ne $? ]]; then #glpk has some strange asserts, try up to 3x before giving up
			echo $3 | ${SIMP} >> ${MF} 2>> ${LOGF}
			if [[ 0 -ne $? ]]; then #glpk has some strange asserts, try up to 3x before giving up
				echo "Error running system from ($1:$2)";
				( echo "Error running system from ($1:$2)"; echo $3 ) >> errors.txt;
				\rm ${SIMP} $(grep -RscIm 1 "${REF}" ${SWF} ${RWF} | cut -d : -f 1 | sort -u) ${MF};
				killall -9 ${SIMP}
				exit;
			fi
		fi
	fi

	if [[ -n "`grep '\[\s*\]\s*\->\s*\[\s*\]\s*:\s*true\s*;' $MF`" ]]; then
		echo "Obtained true on file $1:$2"; echo "$3";
		echo "Got true from system from ($1:$2): $3" >> errors.txt;
		\rm ${SIMP} $(grep -RscIm 1 "${REF}" ${SWF} ${RWF} | cut -d : -f 1 | sort -u) > /dev/null 2> /dev/null;
		killall -9 ${SIMP}
		exit;
	fi
	exit;
}

#Process a file with a system of constraints per line
#Contains one system per line
#Arguments:
#           1: Full path file # assumes this path is the full-path
#           2: 0 if original file, 1 if pre-processed file
process_file() {
	local FP F L SF ALL S i;
	FP=$1;
	if [[ $2 -eq 0 ]]; then
		F=${FP}
		echo "Processing original file ${FP}";
	else
		F=`head -1 ${FP}`;
		L=`sed -n '2{p;q}' ${FP}`;
		echo "Processing pre-processed file ${FP} ( from ${F}:${L} )";
	fi
	SF=${PREFIX}/$(basename ${F}).Simplifier;
	if [[ $2 -eq 0 ]]; then
		ln -s ${Simplify} $SF
	elif [[ ! -e ${SF} ]]; then
		killall -9 `basename ${SF}` > /dev/null 2> /dev/null;
		\rm $(grep -RscIm 1 "${REF}" ${SWF} ${RWF} | cut -d : -f 1 | sort -u) > /dev/null 2> /dev/null;
		return;
	fi
	ALL=${IT}/${F%.deps}.all;
	grep -h "\]\s*\->\s*\[\s*\]" $FP >> $ALL;

	for i in $(grep -hn "\]\s*\->\s*\[" $FP | grep -v "\]\s*\->\s*\[\s*\]" | cut -d : -f 1); do
		wait_for_limits;
		if [[ ! -e ${SF} ]]; then
			killall -9 `basename ${SF}` > /dev/null 2> /dev/null;
			\rm $(grep -RscIm 1 "${REF}" ${SWF} ${RWF} | cut -d : -f 1 | sort -u) > /dev/null 2> /dev/null;
			return;
		fi

		S=$(sed -n "$i{p;q}" $FP);
		if [[ $2 -eq 0 ]]; then
			process_line $F $i "$S" &
		else
			process_line $F $L "$S" &
		fi
	done
	[[ $2 -eq 1 ]] && \rm $FP;
}

get_pID_done() {
	local F ORIGF SF ALL A i;
  jobs -l | awk '($3=="Running"){print $2}' | sort -n > running; #running = List of running PIDs
	ls ${SWF}/ | sort -n | comm - running -2 -3 > toRetire;
	while [[ `cat toRetire | wc -l` -ne 0 ]]; do
  	for i in $(cat toRetire); do    #For i in SWF/* not in running
			F=${SRF}/$i;
			mv ${SWF}/$i $F; #Move file by file all done from work-folder to retired-folder
			ORIGF=`head -1 $F`;
			process_file $F 1;
			SF="${PREFIX}/$(basename $ORIGF).Simplifier";
			[ ! -e $SF ] && continue;
			grep -Rqm 1 "${ORIGF}" ${SWF}; #No more files in the processing folder refers to this file?
			if [[ $? -ne 0 ]]; then
				ALL=${IT}/${ORIGF%.deps}.all;
				if [[ -f $ALL ]]; then
					A=${ORIGF%.deps}.all;
					sort -u $ALL > $A;
					generate_test $A $SF;
				fi
			fi
  	done
		jobs -l | awk '($3=="Running"){print $2}' | sort -n > running;
		ls ${SWF}/ | sort -n | comm - running -2 -3 > toRetire;
	done
	\rm running;
	\rm toRetire;
}


generate_test() {
	local BASE;
	[ ! -f $1 ] && return;
	[ ! -e $2 ] && return;
	BASE=${1%.all};
	BASE=${BASE%.deps};
	echo "Generating test: $2 -c $1 > ${BASE}.test.c 2> ${LG}/`basename ${BASE}.test.c`"
	$2 -c $1 > ${BASE}.test.c 2> ${LG}/`basename ${BASE}.test.c`;
	\rm $2;
}

######################  Start  ############################################

NUM_PROCS="$(lscpu | awk '(NF==2)&&/^CPU\(s\):/{ print $2; exit; }')";
if [ -z $NUM_PROCS ]; then
	NUM_PROCS="$(awk '(NF==3)&&($1=="processor"){p=$3} END{print p+1}' /proc/cpuinfo)"
fi
if [ -z $NUM_PROCS ]; then
	NUM_PROCS=1;
fi
set_NUM_PROCS;

echo "Running with $NUM_PROCS forks"
FD="$(dirname `readlink -f $0`)"
[ -z ${FD} ] && FD="$(dirname `readlink -f $0`)";
[ -z ${FD} ] && FD="./";

ISCC_AWKF=${FD}/isccOutInterpreter.awk
ISCC_IN_AWKF=${FD}/isccInCorrector.awk
Simplify=$(readlink -f `which simplify`)
ISCC=`which iscc`

PREFIX=/tmp
SWF=${PREFIX}/pID;               #Systems workfolder
SRF=${PREFIX}/rID;               #Systems retired folder
 IT=${PREFIX}/intermediary;
 LG=${PREFIX}/logs;

[ -z "$Simplify" ] && "Echo missing Simplifier in the PATH" && exit 1;
[ -z "$ISCC" ] && "Echo missing iscc in the PATH" && exit 1;
[ ! -f "$ISCC_AWKF" ] && "Can't find ISCC output interpreter script" && exit 1;
[ ! -f "$ISCC_IN_AWKF" ] && "Can't find ISCC input fixing script" && exit 1;

[ -e ${SWF} ] && \rm -rf ${SWF};
[ -e ${SRF} ] && \rm -rf ${SRF};
[ -e ${IT}  ] && \rm -rf ${IT};
[ -e ${LG}  ] && \rm -rf ${LG};

touch ${PREFIX}/bla.Simplifier && \rm ${PREFIX}/*.Simplifier;
mkdir ${SWF};
mkdir ${SRF};
mkdir ${IT};
mkdir ${LG};

files=
if [ $# -ne 0 ]; then
	files=$@;
else
	files="$(wc -c `find ver -name '*.deps'` | sort -n | awk '(($1!=0)&&($2!="total")){print $2}')"
fi
if [ -z "$files" ]; then
	echo "No input files"
	exit 1;
fi

for file in $files; do
	file="$(readlink -f $file)";
#Skip files already processed
	if [ -f ${file%.deps}.test.c ]; then
		echo "File ${file%.deps}.test.c already exists, skiping file ${file}.";
		continue;
	fi

#If we have processed systems from previous systems, solve those ones first
	get_pID_done;
#Assure the file has systems
	grep -qm 1 '\]\s*\->\s*\[' $file;
	if [[ $? -ne 0 ]]; then
		echo "File $file has no systems";
		continue;
	fi
#If the file has no variables to remove, generate the .all file
	grep -qvm 1 '\]\s*\->\s*\[\s*\]' $file;
	if [[ $? -ne 0 ]]; then
		echo "File $file has no variables to eliminate, creating .all file";
		ALL=${file%.deps}.all;
		[ "$ALL" != "$file" ] && cp $file $ALL;
		unset ALL;
	fi
	if [ ! -f ${file%.deps}.all ]; then 
		ALL=${IT}/${file%.deps}.all;
		DALL=`dirname $ALL`;
		[ ! -d $DALL ] && mkdir -p $DALL;
		unset DALL;
		[ ! -f $ALL  ] && touch $ALL;
		unset ALL;
		process_file $file 0;
		continue;
	fi
	wait_for_limits;
	SIM=${PREFIX}/`basename ${file%.deps}`.Simplifier;
	[ ! -f $SIM ] && ln -s ${Simplify} ${SIM}
	generate_test ${file%.deps}.all ${SIM} &
done
echo "Finished launching primary systems, waiting for re-entry systems!!"
while [ -n "`ls ${SWF}/`" ]; do
	sleep 0.05;
	get_pID_done;
done
echo "Done"
