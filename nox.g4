grammar nox;

program: statement+;

/* ======================================== */
/* ============== STATEMENTS ============== */
/* ======================================== */

statement:
	return_stm
	| global_stm
	| if_stm
	| while_stm
	| for_stm
	| function_stm
	| break_stm
	| continue_stm
	| assignable_expr assign expression
	| call_expr;

return_stm: 'return' expression;

global_stm: 'global' identifier;

if_stm:
	'if' expression 'then' statement* 'else' statement* 'end';

while_stm: 'while' expression statement* 'end';

for_stm: 'for' identifier 'in' expression statement* 'end';

function_stm:
	'fn' identifier '(' function_args ')' statement* 'end';

function_args: (identifier ',')* (identifier)?;

break_stm: 'break';

continue_stm: 'continue';

assign: '=' | '+=' | '-=' | '*=' | '/=' | '%=';

// not good :/ (never matched)
assignable_expr:
	identifier
	| (expression '.' identifier)
	| (expression '[' expression ']');

// not good :/ (never matched)
call_expr: expression '(' call_args ')';

/* ========================================= */
/* ============== EXPRESSIONS ============== */
/* ========================================= */

expression:
	primary (
		(binary_op primary)
		| ('.' identifier)
		| ('[' expression ']')
		| ('(' call_args ')')
	)*;

primary:
	constant
	| unary_op primary
	| float_number
	| int_number
	| string
	| parent_expr
	| lambda_expr
	| identifier;

constant: 'nil' | 'true' | 'false';

int_number:
	DEC_DIGIT+
	| ('0x' HEX_DIGIT+)
	| ('0o' OCT_DIGIT+)
	| ('0b' BIN_DIGIT+);

float_number: DEC_DIGIT* '.' DEC_DIGIT+;

// TODO : Escape sequences ?
string: ('"' (~'"')* '"') | ('\'' (~'\'')* '\'');

identifier: ID;

parent_expr: '(' expression ')';

binary_op:
	'=='
	| '!='
	| '<'
	| '>'
	| '<='
	| '>='
	| '+'
	| '-'
	| '*'
	| '/'
	| '%'
	| '^'
	| 'or'
	| 'and'
	| 'xor';

unary_op: '-' | 'not';

table_expr:
	'{' (identifier '=' expression ',')* (
		identifier '=' expression
	)? '}';

lambda_expr: 'fn' '(' function_args ')' statement* 'end';

call_args: (expression ',')* (expression)?;

/* ======================================= */
/* ============== TERMINALS ============== */
/* ======================================= */

// TODO : UTF8 identifiers are accepted...
ID: [a-zA-Z_] [a-zA-Z0-9_]*;

DEC_DIGIT: [0-9];

HEX_DIGIT: [0-9] | [a-f];

OCT_DIGIT: [0-7];

BIN_DIGIT: [0-1];

WS: [ \r\n\t] -> skip;

COMMENT: '#' ~[\n]* -> channel(HIDDEN);