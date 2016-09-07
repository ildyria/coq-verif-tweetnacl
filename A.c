/* Hello World program */

#include <stdlib.h>
#include <stdio.h>

typedef unsigned char u8;
typedef unsigned long u32;
typedef unsigned long long u64;
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

static void A(gf o,const gf a,const gf b)
{
  int i;
  for (i = 0;i < 16;++i) o[i]=a[i]+b[i];
}

static void printb64(i64 val)
{
	printf(BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN BYTE_TO_BINARY_PATTERN,
		BYTE_TO_BINARY(val>>56), BYTE_TO_BINARY(val>>48), BYTE_TO_BINARY(val>>40), BYTE_TO_BINARY(val>>32), BYTE_TO_BINARY(val>>24), BYTE_TO_BINARY(val>>16), BYTE_TO_BINARY(val>>8), BYTE_TO_BINARY(val));
}


int main() {
	int i;
	gf a, b, o;

	for (i = 0; i < 16; ++i)
	{
		a[i] = 0;
		b[i] = 0;
		o[i] = 0;
	}

	a[0] = ((long long) 1) << 62;
	b[0] = ((long long) 1) << 62;
	A(o,a,b);

	printb64(a[0]);
	printf("\n");
	printb64(b[0]);
	printf("\n");
	printb64(o[0]);
	printf("\n");

	return 1;
}