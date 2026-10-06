CC ?= gcc
CFLAGS ?= -O2
override CFLAGS += -Wall -Wextra -Werror -std=c11
LDLIBS += -lm

.PHONY: all clean
all: qcal_daq_simulator

qcal_daq_simulator: qcal_daq_simulator.c
	$(CC) $(CPPFLAGS) $(CFLAGS) $(LDFLAGS) -o $@ $< $(LDLIBS)

clean:
	$(RM) qcal_daq_simulator
