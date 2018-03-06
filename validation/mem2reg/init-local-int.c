static int local_int(void)
{
	struct {
		int a;
	} s;

	s.a = 1;
	return s.a;
}

/*
 * check-name: init-local-int
 * check-command: test-linearize $file
 * check-output-ignore
 * check-output-excludes: load\\.
 * check-output-excludes: store\\.
 * check-output-contains: ret.32 *\\$1
 */
