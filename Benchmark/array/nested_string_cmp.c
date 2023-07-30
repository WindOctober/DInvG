int test(const char *name, unsigned int length)
{
	unsigned int i, j;

	char compare[12] = {'\\','<','>','?','"','~','/','\\','[','(',')','!'};

	int ret = 0;	// it's needed to prove the bad_input case


	for (i = 0; i < (length + 1); i++) {

		for (j = 0; j < 12; j++) {
			if (name[i] == compare[j]) {
				ret = -1;
			}
		} 
	}

	if(ret) printf("The input is invalid\n");

	return ret;
}
