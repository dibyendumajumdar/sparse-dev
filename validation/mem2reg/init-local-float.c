static double local_float(void)
{
	struct {
		double a;
	} s;

	s.a = 1.23;
	return s.a;
}

/*
 * check-name: init-local
 * check-command: test-linearize $file
 * check-output-ignore
 * check-output-excludes: load\\.
 * check-output-excludes: store\\.
 */
