// SPDX-License-Identifier: MIT

%{
#define	_GNU_SOURCE
#include <string.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include "codegen.h"

static void yyerror(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
static int yylex(void);
static int yylineno;
static int is_tmpl = 0;
//int yydebug = 1;

static struct ptree *tree(const char *, int, int, struct ptree *, struct ptree *, struct ptree *);
%}
%union {
	int		val;
	char		*str;
	struct ptree	*tree;
	struct nterm	*nt;
}

%token  <str>		TID
%token  <str>		NID
%token  <str>		STR
%token  <str>		TMPL
%token  <val>		INT
%token			EMIT "=>"
%token			EXEC "=="
%token			SIZEB		/* '.B' */
%token			SIZEH		/* '.H' */
%token			SIZEL		/* '.L' */
%token			SIZEQ		/* '.Q' */
%type	<nt>		lhs
%type   <tree>		tree
%type   <val>		cost
%type   <val>		size

%%
start	: entries
	;

entries	: %empty
	| entries entry
	; 
entry	: rule	'\n'
	| error	'\n'
	| 	'\n'	/* empty line */
	;

rule	: lhs ':' tree cost	
				{ mkrule(yylineno, $1, $3, $4, 0, NULL); }
	| lhs ':' tree cost "==" TMPL
				{ mkrule(yylineno, $1, $3, $4, 0, $6); }
	| lhs ':' tree cost "=>" TMPL
				{ mkrule(yylineno, $1, $3, $4, 1, $6); }
	;


lhs	: NID			{ $$ = get_nterm($1); }
	| %empty		{ $$ = get_nterm(""); }
	;

tree	: NID
				{ $$ = tree($1, 0,  0, NULL, NULL, NULL); }
	| TID size
				{ $$ = tree($1, 0, $2, NULL, NULL, NULL); }
	| TID size '(' tree ')'
				{ $$ = tree($1, 1, $2,   $4, NULL, NULL); }
	| TID size '(' tree ',' tree ')'
				{ $$ = tree($1, 2, $2,   $4,   $6, NULL); }
	| TID size '(' tree ',' tree ',' tree ')'
				{ $$ = tree($1, 3, $2,   $4,   $6,   $8); }
	;

size	: %empty		{ $$ = 0; }
	| SIZEB			{ $$ = 1; }
	| SIZEH			{ $$ = 2; }
	| SIZEL			{ $$ = 3; }
	| SIZEQ			{ $$ = 4; }
	;

cost	: %empty		{ $$ = 0; }
	| '[' INT ']'		{ $$ = $2; }
	;
%%
#include <stdarg.h>
#include <ctype.h>

static int nbr_errors;

static void yyerror(const char *fmt, ...)
{
	va_list ap;

	va_start(ap, fmt);
	fprintf(stderr, "error @ line %d: ", yylineno);
	vfprintf(stderr, fmt, ap);
	fprintf(stderr, "\n");
	va_end(ap);
	nbr_errors++;
}

static int yylex(void)
{
	static const char *buffp = "";
	static char *buffer;
	static size_t bufcap;
	static int bufn;
	int c;

	while (1) {
		const char *end;
		const char *buf;
		int n;

		if (is_tmpl) {
			c = *buffp;
			while (isblank(*buffp))
				buffp++;

			end = buffer + bufn;
			if (end[-1] == '\n')
				end--;
			yylval.str = strndup(buffp, end - buffp);
			buffp = end;

			is_tmpl = 0;

			return TMPL;
		}

		switch ((c = *buffp++)) {
		case '\0':	// try to get a new input line
			bufn = getline(&buffer, &bufcap, stdin);
			if (bufn < 0)
				return EOF;
			buffp = buffer;

			// strip comments
			end = strstr(buffp, "//");
			if (end) {
				bufn = end - buffer;
				while (bufn > 0 && isspace(buffer[bufn - 1]))
					bufn--;

				buffer[bufn++] = '\n';
				buffer[bufn] = '\0';
			}

			yylineno++;
			continue;

		// those one must be ignored
		case ' ':
		case '\f':
		case '\t':
			continue;

		// report those as-is
		case '\r':
		case '\n':

		case '(':
		case ')':
		case ',':
		case '[':
		case ']':
		case '<':
		case '>':
		case ';':
		case ':':
			return c;

		case '.':
			if (isalnum(buffp[1]))
				return c;
			switch (*buffp++) {
			case 'B': return SIZEB;
			case 'H': return SIZEH;
			case 'L': return SIZEL;
			case 'Q': return SIZEQ;
			default:  buffp--;
			}

			return c;

		// this one is a bit special
		case '=':
			switch (*buffp) {
			case '>': c = EMIT; break;
			case '=': c = EXEC; break;
			default:
				return c;
			}

			buffp++;
			is_tmpl = 1;
			return c;

		case '0' ... '9':
			n = 0;
			do {
				n = 10 * n + (c - '0');
				c = *buffp++;
			} while (isdigit(c));
			yylval.val = n;
			buffp--;
			return INT;

		case 'A' ... 'Z':
		case 'a' ... 'z':
			buf = buffp - 1;
			while (isalnum(*buffp) || *buffp == '_')
				buffp++;
			yylval.str = strndup(buf, buffp - buf);
			if (lookup_term(yylval.str) != -1)
				return TID;

			return NID;

		// start of string/asm template
		// FIXME: doesn't allow char escaping
		case '"':
			buf = buffp;

			while ((c = *buffp++)) {
				if (c == '"')
					goto case_eos;
			}
			yyerror("missing \" in asm\n");

		case_eos:
			yylval.str = strndup(buf, buffp - buf - 1);
			return STR;

		default:
			if (isprint(c))
				yyerror("invalid char '%c'\n", c);
			else
				yyerror("invalid char '\\x%02x'\n", c);
		}
	}
}

static struct ptree *tree(const char *name, int n, int size, struct ptree *l, struct ptree *r, struct ptree *x)
{
	int op = lookup_term(name);

	if (op == -1) {
		if (n != 0)
			yyerror("invalid terminal: %s\n", name);
	} else {
		if (!check_term(op, n))
			yyerror("arity error for %s/%d\n", name, n);
	}

	return mktree(name, size, l, r, x);
}

int read_md(const char *path)
{
	yyparse();

	return nbr_errors;
}