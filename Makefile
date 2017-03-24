all: ts7500ctl xuartctl spiflashctl sdctl dio
	$(STRIP) $^

ts7500ctl: ts7500ctl.c ispvm.c
	$(CC) -o $@ $^

xuartctl: xuartctl.c
	$(CC) -lutil -o $@ $^

spiflashctl: spiflashctl.c
	$(CC) -lutil -o $@ $^

sdctl: sdctl.c
	$(CC) -o $@ $^

dio: dio.c sbus.c
	$(CC) -lutil -o $@ $^

clean:
	rm -f *.o ts7500ctl xuartctl spiflashctl sdctl dio
