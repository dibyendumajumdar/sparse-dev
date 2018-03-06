void use(int);

double foo(void)
{
	union {
		double	d;
		int	i;
	} u;

	u.d = 1.0;
	use(u.i);
	u.d = 0.0;
	return u.d;
}

/*
 * check-name: access-union1
 * check-command: test-linearize -Wno-decl $file
 * check-known-to-fail
 *
 * check-output-start
foo:
.L0:
	<entry-point>
	setfval.64  %r1 <- 1.000000
	store.64    %r1 <- 0[u]
	load.32     %r2 <- 0[u]
	call        use, %r2
	setfval.64  %r3 <- 0.000000
	ret.64      %r3


 * check-output-end
 * check-output-pattern(1): load\\.
 * check-output-pattern(1): store\\.
 */
