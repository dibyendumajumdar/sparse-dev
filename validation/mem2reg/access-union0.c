typedef unsigned  int u32;
typedef unsigned long u64;

void use(u32);

u32 f0(void)
{
	union {
		u64 b;
		u32 a[2];
	} u;

	u.b = 1;
	return u.a[0];
}


u32 f1(void)
{
	union {
		u64 b;
		u32 a[2];
	} u;

	u.b = 1;
	return u.a[1];
}

/*
 * check-name: access-union0
 * check-command: test-linearize -m64 -Wno-decl $file
 *
 * check-output-ignore
 * check-output-pattern(2): load\\.
 * check-output-pattern(2): store\\.
 * check-output-excludes: ret.32 *\\$1
 */
