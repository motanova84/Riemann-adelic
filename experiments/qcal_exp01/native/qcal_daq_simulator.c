#define _POSIX_C_SOURCE 200809L
/*
 * SYNTHETIC ADC-count source; NOT DMA and NOT a hardware acquisition driver.
 * Quantized synthetic int16, NOT real ADC calibration.
 * int16 full scale is 32768 counts; both carriers peak at 6000 counts.
 * phi(n) = 13.4034 * x0 * sin(2*pi*141.7001*n/fs), x0 in micrometers.
 * The 100 kHz IF requires fs=1 MHz (100 kHz acquisition aliases this IF).
 */
#include <arpa/inet.h>
#include <errno.h>
#include <getopt.h>
#include <inttypes.h>
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

#define HEADER_SIZE 32U
#define SAMPLE_COUNT 342U
#define DATAGRAM_SIZE (HEADER_SIZE + 4U * SAMPLE_COUNT)
#define SAMPLE_RATE 1000000U
#define PI 3.14159265358979323846
#define PACE_GROUP 32U

static void put_u16(uint8_t *out, uint16_t value) {
    out[0] = (uint8_t)value;
    out[1] = (uint8_t)(value >> 8);
}

static void put_u32(uint8_t *out, uint32_t value) {
    for (unsigned i = 0; i < 4; ++i) out[i] = (uint8_t)(value >> (8U * i));
}

static void put_u64(uint8_t *out, uint64_t value) {
    for (unsigned i = 0; i < 8; ++i) out[i] = (uint8_t)(value >> (8U * i));
}

static int parse_uint(const char *text, uint64_t *value) {
    char *end = NULL;
    errno = 0;
    if (*text == '-' || *text == '\0') return -1;
    unsigned long long parsed = strtoull(text, &end, 10);
    if (errno || *end != '\0') return -1;
    *value = (uint64_t)parsed;
    return 0;
}

static int wait_until(const struct timespec *start, uint64_t samples) {
    struct timespec deadline = *start;
    uint64_t seconds = samples / SAMPLE_RATE;
    uint64_t nanos = (samples % SAMPLE_RATE) * 1000U;
    if (seconds > (uint64_t)INT_MAX) return -1;
    deadline.tv_sec += (time_t)seconds;
    deadline.tv_nsec += (long)nanos;
    if (deadline.tv_nsec >= 1000000000L) {
        ++deadline.tv_sec;
        deadline.tv_nsec -= 1000000000L;
    }
    int result;
    do {
        result = clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &deadline, NULL);
    } while (result == EINTR);
    if (result != 0) {
        errno = result;
        perror("clock_nanosleep");
        return -1;
    }
    return 0;
}

int main(int argc, char **argv) {
    const char *host = "127.0.0.1";
    uint64_t port = 5005, packet_limit = 0;
    double x0 = 0.01;
    static const struct option options[] = {
        {"host", required_argument, NULL, 'h'},
        {"port", required_argument, NULL, 'p'},
        {"packets", required_argument, NULL, 'n'},
        {"x0", required_argument, NULL, 'x'},
        {"sample-rate", required_argument, NULL, 'r'},
        {NULL, 0, NULL, 0}
    };
    int option;
    while ((option = getopt_long(argc, argv, "", options, NULL)) != -1) {
        uint64_t parsed;
        switch (option) {
        case 'h': host = optarg; break;
        case 'p':
            if (parse_uint(optarg, &port) || port == 0 || port > 65535) goto usage;
            break;
        case 'n':
            if (parse_uint(optarg, &packet_limit)
                || packet_limit > UINT64_MAX / SAMPLE_COUNT) goto usage;
            break;
        case 'r':
            if (parse_uint(optarg, &parsed) || parsed != SAMPLE_RATE) goto usage;
            break;
        case 'x': {
            char *end = NULL;
            errno = 0;
            x0 = strtod(optarg, &end);
            if (errno || end == optarg || *end || !isfinite(x0)
                || x0 < 0.0 || x0 > 100.0) goto usage;
            break;
        }
        default: goto usage;
        }
    }
    if (optind != argc) goto usage;
    struct sockaddr_in destination;
    memset(&destination, 0, sizeof(destination));
    destination.sin_family = AF_INET;
    destination.sin_port = htons((uint16_t)port);
    if (inet_pton(AF_INET, host, &destination.sin_addr) != 1) goto usage;
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) {
        perror("socket");
        return EXIT_FAILURE;
    }
    struct timespec start;
    if (clock_gettime(CLOCK_MONOTONIC, &start) != 0) {
        perror("clock_gettime");
        close(fd);
        return EXIT_FAILURE;
    }
    fprintf(stderr, "SYNTHETIC (NOT DMA): fs=%u Hz IF=100000 Hz "
            "f0=141.7001 Hz injected_x0=%.9g um kappa=13.4034 rad/um; "
            "A=reference IF, B=modulated IF; "
            "int16 scale=1/32768, peak=6000 counts; NOT hardware calibration\n",
            SAMPLE_RATE, x0);
    uint64_t sequence = 0, first = 0;
    while (packet_limit == 0 || sequence < packet_limit) {
        uint8_t datagram[DATAGRAM_SIZE];
        memcpy(datagram, "QCL1", 4);
        datagram[4] = 1;
        datagram[5] = 0;
        put_u16(datagram + 6, HEADER_SIZE);
        put_u64(datagram + 8, sequence);
        put_u64(datagram + 16, first);
        put_u32(datagram + 24, SAMPLE_RATE);
        put_u32(datagram + 28, SAMPLE_COUNT);
        for (unsigned j = 0; j < SAMPLE_COUNT; ++j) {
            uint64_t index = first + j;
            double carrier = 2.0 * PI * (double)(index % 10U) / 10.0;
            double seconds = (double)index / SAMPLE_RATE;
            double phase = 13.4034 * x0 * sin(2.0 * PI * 141.7001 * seconds);
            int16_t a = (int16_t)lround(6000.0 * cos(carrier));
            int16_t b = (int16_t)lround(6000.0 * cos(carrier + phase));
            put_u16(datagram + HEADER_SIZE + 2U * j, (uint16_t)a);
            put_u16(datagram + HEADER_SIZE + 2U * SAMPLE_COUNT + 2U * j, (uint16_t)b);
        }
        ssize_t sent = sendto(fd, datagram, sizeof(datagram), 0,
                              (struct sockaddr *)&destination, sizeof(destination));
        if (sent != (ssize_t)sizeof(datagram)) {
            if (sent < 0) perror("sendto");
            else fprintf(stderr, "short UDP send\n");
            close(fd);
            return EXIT_FAILURE;
        }
        first += SAMPLE_COUNT;
        ++sequence;
        /* Bounded bursts, absolute monotonic deadlines; no RT scheduling. */
        if ((sequence % PACE_GROUP == 0
             || (packet_limit != 0 && sequence == packet_limit))
            && wait_until(&start, first) != 0) {
            close(fd);
            return EXIT_FAILURE;
        }
        if (first > UINT64_MAX - SAMPLE_COUNT) break;
    }
    if (close(fd) != 0) {
        perror("close");
        return EXIT_FAILURE;
    }
    return EXIT_SUCCESS;

usage:
    fprintf(stderr, "Usage: %s [--host IPv4] [--port 1..65535] "
            "[--packets N (0=continuous)] [--x0 micrometers] "
            "[--sample-rate 1000000]\n", argv[0]);
    return EXIT_FAILURE;
}
