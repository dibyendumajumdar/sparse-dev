typedef double        dbl;
typedef unsigned long u64;

void use(u64);

u64 foo(void)
{
	union {
		dbl f;
		u64 i;
	} u;

	u.f = 1.0;
	use(u.i);
	u.f = 0.0;
	return u.f;
}

/*
 * check-name: access-union2
 * check-command: test-linearize -Wno-decl $file
 *
 * check-output-ignore
 * check-output-pattern(1): load\\.
 * check-output-pattern(1): store\\.
 */
