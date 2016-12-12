#include <stdio.h>
#include <stdbool.h>

typedef long long i64;
typedef i64 gf[16];


#define BYTE_TO_BINARY_PATTERN "%c%c%c%c%c%c%c%c"
#define BYTE_TO_BINARY(byte)  \
  (byte & 0x80 ? '1' : '0'), \
  (byte & 0x40 ? '1' : '0'), \
  (byte & 0x20 ? '1' : '0'), \
  (byte & 0x10 ? '1' : '0'), \
  (byte & 0x08 ? '1' : '0'), \
  (byte & 0x04 ? '1' : '0'), \
  (byte & 0x02 ? '1' : '0'), \
  (byte & 0x01 ? '1' : '0')


static void print_bin64(i64 val)
{
	printf(" "BYTE_TO_BINARY_PATTERN" "BYTE_TO_BINARY_PATTERN" "BYTE_TO_BINARY_PATTERN" "BYTE_TO_BINARY_PATTERN,
		BYTE_TO_BINARY(val>>56), BYTE_TO_BINARY(val>>48), BYTE_TO_BINARY(val>>40), BYTE_TO_BINARY(val >> 32));
	printf(" "BYTE_TO_BINARY_PATTERN" "BYTE_TO_BINARY_PATTERN" "BYTE_TO_BINARY_PATTERN" "BYTE_TO_BINARY_PATTERN,
		BYTE_TO_BINARY(val>>24), BYTE_TO_BINARY(val>>16), BYTE_TO_BINARY(val>>8), BYTE_TO_BINARY(val));
	printf("\n");
}

static void print_o(gf o)
{
    for (int j = 0; j < 16; ++j)
	{
		printf("%2i: ", j);
		print_bin64(o[j]);
	}

}

static void car25519(gf o, bool b)
{
  int i;
  i64 c;
  for (i = 0;i < 16;++i) {
    // o[i]+=(1LL<<16);
    c=o[i]>>16;
    // o[(i+1)*(i<15)]+=c-1+37*(c-1)*(i==15);
    o[(i+1)*(i<15)]+=c+37*(c)*(i==15);
    o[i]-=c<<16;

    if(b){
		// added to have a look at what is going on in there
		printf("%2i : ---------------------------------------------\n",i);
		for (int j = 0; j < 16; ++j)
		{
			printf("%2i: ", j);
			print_bin64(o[j]);
		}
    }
  }
}

int main(int argc, char const *argv[])
{
	gf o;
	i64 val = 0xFFFF;
	for (int i = 0; i < 16; ++i)
	{
		o[i] = val;
	}

	o[15] = val | (val << 32);
	for (int i = 0; i < 16; ++i)
	{
		printf("%2i: ", i);
		print_bin64(o[i]);
	}


	printf("carry 1\n");
	car25519(o,0);
	printf("result carry 1:__________________________________________\n");
	print_o(o);

	printf("carry 2\n");
	car25519(o,0);
	printf("result carry 2:__________________________________________\n");
	print_o(o);

	printf("####################################################\n");

	val = -0xFFFFF;
	for (int i = 0; i < 16; ++i)
	{
		o[i] = val;
	}
	print_o(o);

	print_bin64(o[0]);
    o[0]+=(1LL<<16);
    i64 c;
    printf("o[0]+=(1LL<<16)\n");
	print_bin64(o[0]);

    c=o[0]>>16;
    printf("c=o[0]>>16;\n");
	print_bin64(c);

    o[1]+=c-1;
    printf("o[1]+=c-1;\n");
	print_bin64(o[1]);

    o[0]-=c<<16;
    printf("o[0]-=c<<16;\n");
	print_bin64(o[0]);

	printf("result carry step 1:_____________________________________\n");
	print_o(o);

	printf("####################################################\n");

	val = -0xFFFFF; // -2^20 if I'm not mistaken
	for (int i = 0; i < 16; ++i)
	{
		o[i] = val;
	}
	print_o(o);

	car25519(o,0);
	printf("result carry 1:__________________________________________\n");
	print_o(o);
	car25519(o,0);
	printf("result carry 2:__________________________________________\n");
	print_o(o);
	car25519(o,0);
	printf("result carry 3:__________________________________________\n");
	print_o(o);

	return 0;
}
