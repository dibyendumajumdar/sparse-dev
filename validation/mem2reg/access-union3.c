typedef double        dbl;
typedef unsigned long u64;

void use(u64);

static dbl foo(void)
{
	union {
		dbl f;
		u64 i;
	} u;

	u.i = 123;
	return u.f;
}

/*
 * check-name: access-union3
 * check-command: test-linearize -fdump-ir=mem2reg $file
 *
 * check-output-ignore
 * check-output-pattern(1): load\\.
 * check-output-pattern(1): store\\.
 */
