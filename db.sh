#!/bin/sh

usage()
{
	echo "Usage: $(basename $0) [-l] DBFILE"
	echo "Start database daemon on DBFILE or lock DBFILE."
	echo ""
	echo "Options:"
	echo "  -l   lock DBFILE, don't start database daemon"
	echo ""
	echo "Examples:"
	echo ""
}

dblock()
{
	TIMEOUT="3"
	FILELOCKS=""
	ALRMPID=""
	SIGNALS="1 2 3 15"

	test $# -gt 0 || exit

	cleanup()
	{
		#echo 'cleaning up...' >&2
		trap '' $SIGNALS
		rm -rf $FILELOCKS
		test -n "$ALRMPID" && kill $ALRMPID >/dev/null 2>&1
	}

	sigalrm()
	{
		#echo 'got SIGALRM...' >&2
		ALRMPID=""
		exit 1
	}

	setalarm()
	{
		local secs="$1"
		trap 'sigalrm' 14
		sleep $secs && kill -ALRM $$ >/dev/null 2>&1 &
		ALRMPID=$!
	}

	trap 'cleanup; exit' 0 $SIGNALS
	setalarm $TIMEOUT

	for f in $*; do
		touch "$f".lock.$$ || exit
		FILELOCKS="$FILELOCKS $f.lock.$$"
		while ! ln "$f.lock.$$" "$f.lock" >/dev/null 2>&1 && \
		    test $(stat -c '%h' "$f.lock") 2>/dev/null -eq 2; do
			sleep 1
		done
		FILELOCKS="$FILELOCKS $f.lock"
	done

	kill -TERM $ALRMPID >/dev/null 2>&1

	echo 'OK'

	while read line; do
		true
	done

	exit 0
}

while getopts "l" opt
do
	case $opt in
	l)	lockflag=1;;
	\?)	usage; exit 1;;
	esac
done
shift $((OPTIND-1))

test $# -ge 1 || { usage; exit 1; }

DBFILE="$1"

test "$lockflag" && { dblock "$DBFILE"; exit 0; }

awk -v DBFILE="$DBFILE" -v LOCKCMD="$0 -l \"$DBFILE\"" '
# Adds attribute name-value pair to entry.
function addattr(e, name, value,	idx)
{
	if ((idx = name2i(name)) != "")
		e[idx] = value
}

# Strips trailing and preceding spaces from string s.
function stripspc(s)
{
	sub(/^[ \t]*/, "", s)
	sub(/[ \t]*$/, "", s)
	return s
}

# Prints message to stdout
function msg(code, text)
{
	printf "%d %s\n", code, text
}

# Returns i-th char from the string.
function chr(s, i)
{
	return substr(s, i, 1)
}

# Makes a copy of an array.
function cparray(dst, src,	val)
{
	delete dst
	for (val in src) {
		if (isarray(src[val]))
			cparray(dst[val], src[val])
		else
			dst[val] = src[val]
	}
}

# Clears all array keys.
function clrarray(a,	val)
{
	for (val in a)
		delete a[val]
}

# Compares two variables as numbers.
function intcmp(a, b)
{
	if (0+a > 0+b)
		return 1
	else if (0+a < 0+b)
		return -1
	return 0
}

# Compares two variables as strings.
function strcmp(a, b)
{
	if (""a > ""b)
		return 1
	else if (""a < ""b)
		return -1
	return 0
}

# Returns field specifier character in format string for the field.
function dbfmt(fno)
{
	if (fno in _dbfmt)
		return _dbfmt[fno]
	return -1
}

# Returns field number of database element from its name.
function name2i(field)
{
	if (field in _name2i)
		return _name2i[field]
	return -1
}

# Returns name from field number of database element.
function i2name(i,	v)
{
	for (v in _name2i)
		if (_name2i[v] == i)
			return v
	return "???"
}

function op2name(op)
{
	if (op in _op2name)
		return _op2name[op]
	return "???"
}

# Returns a string with formatted printout of database element fields.
function fmtsprintf(fmt, id, e,		i, c, s, n, t)
{
	s = ""
	for (i=1; (c = chr(fmt, i)); i++) {
		if (c == "%") {
			if ((c = chr(fmt, ++i)) == "%")
				s = s "%"
			else if ((n = dbfmt(c)) >= 0) {
				t = dbscheme(n)
				if (t == F_INTEGER)
					s = s 0+(n>0 ? e[n] : id)
				else if (t == F_STRING)
					s = s "" (n>0 ? e[n] : id)
				else if (t == F_DATE)
					s = s 0+(n>0 ? e[n] : id)
				else
					s = s "" (n>0 ? e[n] : id)
			} else
				s = s "%" c
		} else
			s = s c
	}
	return s
}

#
# Lexical scanner definitions and functions.
# 
BEGIN {
	NOW = 0
	NEXT = 1

	T_TYPE = 0
	T_VALUE = 1

	TK_OP = 0	# operator value is in T_VALUE field
	TK_WORD = 1
	TK_LBRACKET = 2
	TK_RBRACKET = 3
	TK_INT = 4
	TK_STRING = 5
	TK_OR = 6
	TK_AND = 7
	TK_NOT = 8
	TK_EOL = 255
	TK_INVAL = -1

	reswords["or"] = TK_OR
	reswords["and"] = TK_AND
	reswords["not"] = TK_NOT

	# Promote array type on tk before use.
	tk[NOW][T_TYPE] = TK_INVAL
	tk[NOW][T_VALUE] = ""
	tk[NEXT][T_TYPE] = TK_INVAL
	tk[NEXT][T_VALUE] = ""
	# tk[NEXT] is not present yet, clear it
	clrarray(tk[NEXT])
}

# Real routine to get a token
function gettokenreal(tkn,	c, type)
{
	clrarray(tkn)

	for (;;) {
		c = chr(exprtext, exprpos)
		switch (c) {
		case "":
			tkn[T_TYPE] = TK_EOL
			tkn[T_VALUE] = ""
			return TK_EOL
		case /[0-9]/:
			tkn[T_TYPE] = TK_INT
			tkn[T_VALUE] = ""
			do {
				tkn[T_VALUE] = tkn[T_VALUE] c
				exprpos++
			} while ((c = chr(exprtext, exprpos)) ~ /[0-9]/)
			return TK_INT
		case /[_a-zA-Z]/:
			tkn[T_TYPE] = TK_WORD
			tkn[T_VALUE] = c
			exprpos++
			while ((c = chr(exprtext, exprpos)) ~ /[_a-zA-Z0-9]/) {
				tkn[T_VALUE] = tkn[T_VALUE] c
				exprpos++
			}
			if (tolower(tkn[T_VALUE]) in reswords) {
				type = reswords[tolower(tkn[T_VALUE])]
				tkn[T_TYPE] = type
				tkn[T_VALUE] = tolower(tkn[T_VALUE])
				return type
			}		
			return TK_WORD
		case "'\''": # This is a single quote character.
			tkn[T_TYPE] = TK_STRING
			tkn[T_VALUE] = ""
			exprpos++
			while ((c = chr(exprtext, exprpos)) != "'\''" && c) {
				if (c == "\\") {
					c = chr(exprtext, ++exprpos)
					switch (c) {
					# literally backslash or single quote
					case "\\": break
					case "'\''": break
					# next go well-known ASCII control characters
					case "a": c = "\a"; break
					case "b": c = "\b"; break
					case "t": c = "\t"; break
					case "n": c = "\n"; break
					case "v": c = "\v"; break
					case "f": c = "\f"; break
					case "r": c = "\r"; break
					}
				}
				tkn[T_VALUE] = tkn[T_VALUE] c
				exprpos++
			}
			if (c == "'\''") {
				exprpos++
				return TK_STRING
			} else {
				printf "gettoken: unterminated string constant at pos %d", exprpos
				return TK_INVAL
			}
		case "(":
			tkn[T_TYPE] = TK_LBRACKET
			tkn[T_VALUE] = "("
			exprpos++
			return TK_LBRACKET
		case ")":
			tkn[T_TYPE] = TK_RBRACKET
			tkn[T_VALUE] = ")"
			exprpos++
			return TK_RBRACKET
		case "=":
			tkn[T_TYPE] = TK_OP
			tkn[T_VALUE] = "="
			exprpos++
			return TK_OP
		case "!":
			if (chr(exprtext, exprpos+1) == "=") {
				tkn[T_TYPE] = TK_OP
				tkn[T_VALUE] = "!="
				exprpos += 2
			} else {
				printf "gettoken: invalid operator at pos %d\n", exprpos
				return TK_INVAL
			}
			return TK_OP
		case "~":
			tkn[T_TYPE] = TK_OP
			tkn[T_VALUE] = "~"
			exprpos++
			return TK_OP
		case ">":
		case "<":
			tkn[T_TYPE] = TK_OP
			if (chr(exprtext, exprpos+1) == "=") {
				switch (c) {
				case ">": tkn[T_VALUE] = ">="; break
				case "<": tkn[T_VALUE] = "<="; break
				}
				exprpos += 2
			} else {
				tkn[T_VALUE] = c
				exprpos++
			}
			return TK_OP
		default:
			exprpos++
			break
		}
	}
}

# Returns next token type, current token is not modified.
function nexttoken()
{
#	clrarray(tk[NEXT])
	if (T_VALUE in tk[NEXT]) {
	} else {
		gettokenreal(tk[NEXT])
	}
	return tk[NEXT][T_TYPE]
}

# Returns and consumes a token.
function gettoken()
{
	if (T_VALUE in tk[NEXT]) {
		tk[NOW][T_TYPE] = tk[NEXT][T_TYPE]
		tk[NOW][T_VALUE] = tk[NEXT][T_VALUE]
		clrarray(tk[NEXT])
	} else {
		gettokenreal(tk[NOW])
	}
	return tk[NOW][T_TYPE]
}

#
# Expression evaluation.
#

BEGIN {
	# expression operator structure fields
	N_FIELD	= 0	# entry field we operate on (E_ID, E_MD5, ...)
	N_OP = 1	# operator (O_EQ, O_GET, ...)
	N_ROP = 2	# right side of the operator (string or integer)
	N_NEG = 3	# negation
	N_SUBEXPR = 4	# subexpression (if  N_FIELD is set to -1)

	# operators
	O_EQ = 0
	O_GT = 1
	O_LT = 2
	O_GE = 3
	O_LE = 4
	O_NE = 5
	O_RE = 6

	_op2name[O_EQ] = "="
	_op2name[O_GT] = ">"
	_op2name[O_LT] = "<"
	_op2name[O_GE] = ">="
	_op2name[O_NE] = "!="
	_op2name[O_RE] = "~"
}

# Evaluates a single operator expression.
function evalop(opexpr, e,	rc, res, type)
{
	res = 0
	type = dbscheme(opexpr[N_FIELD])
	if (type == F_STRING) {
		if (opexpr[N_OP] == O_RE) {
			if (e[opexpr[N_FIELD]] ~ opexpr[N_ROP])
				res = 1
			return opexpr[N_NEG] ? !res : res
		}
		rc = strcmp(e[opexpr[N_FIELD]], opexpr[N_ROP])
	} else if (type == F_INTEGER || type == F_DATE)
		rc = intcmp(e[opexpr[N_FIELD]], opexpr[N_ROP])
	else
		print "evalop: should not reach!" >"/dev/stderr"
	
	if (opexpr[N_OP] == O_EQ && rc == 0)
		res = 1
	else if (opexpr[N_OP] == O_GT && rc > 0)
		res = 1
	else if (opexpr[N_OP] == O_LT && rc < 0)
		res = 1
	else if (opexpr[N_OP] == O_GE && rc >= 0)
		res = 1
	else if (opexpr[N_OP] == O_LE && rc <= 0)
		res = 1
	else if (opexpr[N_OP] == O_NE && rc != 0)
		res = 1
	return opexpr[N_NEG] ? !res : res
}

# Evaluates a complete expression for entry `e`.
function evalexpr(expr, e,		i, j, rc, res)
{
	res = 0
	for (i=0; i in expr; i++) {
		for (j=0; j in expr[i]; j++) {
			if (expr[i][j][N_FIELD] < 0)
				rc = evalexpr(expr[i][j][N_SUBEXPR], e)
			else
				rc = evalop(expr[i][j], e)
			if (expr[i][j][N_NEG])
				rc = !rc
			if (!rc)
				break
		}
		if (rc) { res = 1; break }
	}
	return res
}

#
# Syntactic analyzer.
#
# This function performs syntactic analysis of expression and constructs
# its tree presentation in expr. Arguments i and j represent
# correspondinly OR and AND position in an expression tree.
#
# Expression tree:
#
#             j=0    j=1    j=2
#  i=0 [OR]->[AND]->[AND]->[AND]
#  i=1 [OR]->[AND]-...->[AND]
#     ...
#  i=N [OR]->[AND]-...->[AND]
#
function parseexpr(expr, i, j,		tok, n, op)
{
	if ((tok = gettoken()) == TK_LBRACKET) {
		expr[i][j][N_FIELD] = -1
		# Force awk to think about expr[i][j][N_SUBEXPR] as an array.
		expr[i][j][N_SUBEXPR][0][0][N_OP] = -1
		if (parseexpr(expr[i][j][N_SUBEXPR], 0, 0))
			return 1
		if (gettoken() != TK_RBRACKET) {
			printf "parseexpr: missing right brace in subexpression\n" >>"/dev/stderr"
			return 1
		}
		return restexpr(expr, i, j)
	} else if (tok == TK_NOT) {
		expr[i][j][N_NEG] = !expr[i][j][N_NEG]
		if (parseexpr(expr, i, j))
			return 1
	} else if (tok == TK_WORD) {
		if ((n = name2i(tk[NOW][T_VALUE])) < 0) {
			printf "parseexpr: invalid field name %s\n", tk[NOW][T_VALUE] >>"/dev/stderr"
			return 1
		}
		expr[i][j][N_FIELD] = n
		if (gettoken() != TK_OP) {
			printf "parseexpr: expected operator in expression\n" >>"/dev/stderr"
			return 1
		}
		switch (tk[NOW][T_VALUE]) {
		case "=": op = O_EQ; break
		case ">": op = O_GT; break
		case "<": op = O_LT; break
		case ">=": op = O_GE; break
		case "<=": op = O_LE; break
		case "!=": op = O_NE; break
		case "~": op = O_RE; break
		}
		expr[i][j][N_OP] = op
		if (nexttoken() != TK_INT && nexttoken() != TK_STRING) {
			printf "parseexpr: expected string or integer constant in expression\n" >>"/dev/stderr"
			return 1
		}
		gettoken()
		expr[i][j][N_ROP] = tk[NOW][T_VALUE]
		return restexpr(expr, i, j)
	}

	return 0
}

function restexpr(expr, i, j,	tok)
{
	if (nexttoken() == TK_AND || nexttoken() == TK_OR) {
		if ((tok = gettoken()) == TK_AND) {
			return parseexpr(expr, i, j+1)
		} else if (tok == TK_OR) {
			return parseexpr(expr, i+1, 0)
		}
	}
	return 0
}

function parse()
{
	return (!parseexpr(expr, 0, 0) && gettoken() == TK_EOL) ? 0 : 1
}

function printexpr(expr,	i, j)
{
	for (i=0; i in expr; i++) {
		if (i > 0) printf " OR "
		for (j=0; j in expr[i]; j++) {
			if (j > 0) printf " AND "
			if (expr[i][j][N_FIELD] < 0) {
				if (expr[i][j][N_NEG])
					printf "NOT"
				printf " ( "
				printexpr(expr[i][j][N_SUBEXPR])
				printf " ) "
			} else {
				if (expr[i][j][N_NEG]) printf "NOT "
				printf "%s ", i2name(expr[i][j][N_FIELD])
				printf "%s ", op2name(expr[i][j][N_OP])
				printf "%s",  expr[i][j][N_ROP]
			}
		}
	}
}

# Returns entry field type provided field number.
function dbscheme(field)
{
	if (field in _dbscheme)
		return _dbscheme[field]
	return -1
}

# Reads database scheme from scheme file.
function readscheme(schemefile,		i, t, n, c, nfield, nline)
{
	nfield = 1; nline = 0
	while ((getline ln < schemefile) > 0) {
		nline++
		field = stripspc(substr(ln, 1, index(ln, ":")-1))
		type = stripspc(substr(ln, index(ln, ":")+1))
		switch (chr(type, 1)) {
		case "i": t = F_INTEGER; break
		case "s": t = F_STRING; break
		case "d": t = F_DATE; break
		default: printf "readscheme: unknown field type " \
				"in schema file '\''%s'\'' on line %d\n", \
				schemefile, nline >"/dev/stderr"
		}
		i = 2; n = -1
		while (chr(type, i)) {
			if (chr(type, i) == ",") {
				if (chr(type, i+1) == "k") {
					# This field is an index.
					n = 0
					i += 2
				} else if (chr(type, i+1) == "%") {
					# Field specifier character.
					c = chr(type, i+2)
					i += 3
				}
			} else
				break
		}
		if (n < 0)
			n = nfield++
		fmtscheme = fmtscheme (fmtscheme ? ":%"c : "%"c)
		_dbscheme[n] = t
		c ? _dbfmt[c] = n : 0
		_name2i[field] = n
	}
}

# Checks validity of the database entry.
function validentry(e)
{
	if (E_ID in e)
		return 1
	return 0
}

# Adds entry to database.
function addentry(e, replace,	i, id)
{
	id = e[E_ID]

	if (!replace && id in db)
		return 1
	for (i in e) {
		if (i == E_ID)
			continue
		db[id][i] = e[i]
	}
	return 0
}

# Matches filter expression against database entry.
function filtermatch(id, e,		tmp)
{
	if (exprpos) {
		cparray(tmp, e)
		tmp[E_ID] = id
		return evalexpr(expr, tmp)
	} else
		return 1
}

# Atomically replaces file `from` to file `to`.
function replace(from, to)
{
	if (system("ln " from " " to"."PROCINFO["pid"]))
		return 1
	if (system("mv " from " " to " || { unlink " to"."PROCINFO["pid"]"; return 1;}"))
		return 1
	system("unlink "to"."PROCINFO["pid"])
}

# Outputs database in its storage format.
function outputdb(file)
{
	# Truncate file to 0 bytes.
	printf "" >file

	for (id in db) {
		printf "%s: %s\n", i2name(E_ID), id >>file
		for (n in db[id]) {
			printf "%s: %s\n", i2name(n), db[id][n] >>file 
		}
		printf "\n" >>file
	}
}

# This function locks database by running lock coprocess.
function lockdb()
{
	# LOCKCMD is provided by command line variable assignment.
	lockcoproc = LOCKCMD
	lockcoproc |& getline ln
	return ln == "OK"
}

# This function closes pipes to lock coprocess releasing locks.
function unlockdb()
{
	close(lockcoproc)
}

function endcmd()
{
	printf "\n"
	fflush("/dev/stdout")
	next
}

BEGIN {
	# index field is always numbered 0
	E_ID = 0

	# database schema types
	F_INTEGER = 0
	F_STRING = 1
	F_DATE = 2

	DBFILE = DBFILE ? DBFILE : "db"
	DBFILENEW = DBFILE ".new"
	DBSCHEME = DBFILE ".scheme"
	dbdirty = 0	# set to 1 if entries changed/insered

	#fmtentry = "%i:%b:%d:%n:%s:%k:%v:%c"
	exprpos = 0	# LIST shows all entries, no filter expression
	
	if (!lockdb()) {
		printf "lockdb: can'\''t obtain database lock!\n" >"/dev/stderr"
		exit 2
	}
	# Obtain database scheme.
	readscheme(DBSCHEME)

	# Set default listing format.
	fmtentry = fmtscheme

	while (getline line <DBFILE > 0) {
		if (line == "") {
			if (validentry(e))
				addentry(e, 1)
			delete(e)
		} else if (i = index(line, ":")) {
			name = stripspc(substr(line, 1, i-1))
			value = stripspc(substr(line, i+1))
			addattr(e, tolower(name), value)
		}
	}

	if (validentry(e))
		addentry(e, 1)
	delete(e)

	msg(0, "OK 0.1")
	fflush("/dev/stdout")
}

$1 == "DELETE" {
	for (i=2; i<=NF; i++) {
		key = $i
		if (key in db) {
			delete db[key]
			dbdirty = 1
		}
	}
	msg(0, "ok")
	endcmd()
}

$1 == "INSERT" {
#	if (tolower($2) == "file")
#		file = $3
#	else
#		file = "/dev/stdin"

	delete(e)	
	while (getline line > 0) {
		if (line == "")
			break
		if (i = index(line, ":")) {
			name = stripspc(substr(line, 1, i-1))
			value = stripspc(substr(line, i+1))
			addattr(e, tolower(name), value)
		}
	}
	if (validentry(e)) {
		dbdirty = 1
		addentry(e, 1)
		msg(0, "ok")
	} else {
		msg(202, "invalid entry data")
	}
#	if (file != "/dev/stdin")
#		close(file)
	endcmd()
}

$1 == "SETFMT" {
	saved_FS = FS
	$0 = stripspc(substr($0, length("SETFMT")+1))
	FS = ""
	# remove single quote character from format string
	if (chr($0, 1) == "'\''")
		$0 = substr($0, 2)
	fmtentry = $0 ? $0 : fmtscheme
	msg(0, "ok")
	FS = saved_FS
	endcmd()
}

$1 == "SETFILTER" {
	$1 = ""
	exprtext = $0
	if (exprtext) {
		exprpos = 1
		delete expr
		if (parse() != 0) {
			msg(201, "invalid filter expression")
			exprpos = 0
		} else {
			msg(0, "ok")
			#printexpr(expr)
		}
	} else {
		exprpos = 0
		msg(0, "ok")
	}
	endcmd()
}

$1 == "SHOWSCHEME" {
	msg(0, "ok")
	for (v in _name2i) {
		n = name2i(v)
		for (c in _dbfmt)
			if (dbfmt(c) == n)
				break
		printf("%s %s%s\n", v, name2i(v) == 0 ? "k," : "", c ? "%"c : "")
	}
	endcmd()
}

$1 == "LIST" {
	msg(0, "ok")
	for (id in db) {
		if (filtermatch(id, db[id])) {
			printf "%s\n", fmtsprintf(fmtentry, id, db[id])
		}
	}
	endcmd()
}

$1 != "" {
	msg(400, "unknown command")
	endcmd()
}

END {
	if (dbdirty) {
		outputdb(DBFILENEW)
		if (replace(DBFILENEW, DBFILE))
			printf "Error: failed to save "
			       "database changes!\n" >"/dev/stderr"
	}
	unlockdb()
}
'
