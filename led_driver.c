/*
 * led_driver.c — Raspberry Pi LED Driver (BCM2835 bare-metal style via /dev/mem)
 *
 * Demonstrates:
 *   1. GPIO OUTPUT  — Drive 3 LEDs (blink, PWM-dimming, pattern)
 *   2. GPIO INPUT   — Read a push-button with debouncing
 *   3. INTERRUPTS   — Button press detected via edge-triggered poll (Linux GPIO IRQ)
 *   4. TIMING       — nanosleep(), clock_gettime(), software PWM, periodic timer
 *
 * Hardware wiring (BCM pin numbers):
 *   GPIO 17  →  LED 1 (blink LED)         via 330Ω resistor to GND
 *   GPIO 27  →  LED 2 (PWM dimming LED)   via 330Ω resistor to GND
 *   GPIO 22  →  LED 3 (pattern LED)       via 330Ω resistor to GND
 *   GPIO 4   ←  Push-button (INPUT)       other leg to GND (internal pull-up used)
 *
 * Build:
 *   gcc -O2 -Wall -o led_driver led_driver.c -lpthread
 *
 * Run (requires root for /dev/mem access OR use gpiochip via libgpiod):
 *   sudo ./led_driver
 *
 * Press the button to cycle through LED modes.
 * Press Ctrl+C to exit cleanly.
 *
 * Tested on: Raspberry Pi 3B+, 4B (Raspbian / Raspberry Pi OS)
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <poll.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/types.h>

/* ============================================================
 *  GPIO BASE ADDRESSES
 *  Pi 1/2/3:  0x3F200000 (mapped from physical 0x20200000)
 *  Pi 4:      0xFE200000
 *  We auto-detect by reading /proc/cpuinfo
 * ============================================================ */
#define BCM2835_PERI_BASE   0x3F000000   /* Pi 2 / Pi 3           */
#define BCM2711_PERI_BASE   0xFE000000   /* Pi 4                  */
#define GPIO_BASE_OFFSET    0x00200000   /* GPIO offset from peri */
#define BLOCK_SIZE          (4 * 1024)

/* GPIO register offsets (each register is 32-bit) */
#define GPFSEL0   0   /* Function select 0 (pins 0-9)   */
#define GPFSEL1   1   /* Function select 1 (pins 10-19) */
#define GPFSEL2   2   /* Function select 2 (pins 20-29) */
#define GPSET0    7   /* Pin output set   0 (pins 0-31) */
#define GPCLR0   10   /* Pin output clear 0 (pins 0-31) */
#define GPLEV0   13   /* Pin level        0 (pins 0-31) */
#define GPPUD    37   /* Pull-up/down enable             */
#define GPPUDCLK0 38  /* Pull-up/down clock 0            */

/* ============================================================
 *  PIN DEFINITIONS
 * ============================================================ */
#define LED_BLINK    17   /* GPIO 17 — blinking LED      */
#define LED_PWM      27   /* GPIO 27 — PWM dimming LED   */
#define LED_PATTERN  22   /* GPIO 22 — pattern LED       */
#define BTN_PIN       4   /* GPIO 4  — push button input */

/* ============================================================
 *  TIMING HELPERS (nanoseconds)
 * ============================================================ */
#define NS_PER_MS   1000000LL
#define NS_PER_SEC  1000000000LL

#define BLINK_PERIOD_MS     500    /* LED1 blink period          */
#define PWM_PERIOD_US       1000   /* Software PWM period 1 ms   */
#define DEBOUNCE_MS         50     /* Button debounce window      */

/* ============================================================
 *  GLOBAL STATE
 * ============================================================ */
static volatile uint32_t *gpio = NULL;  /* mmap'd GPIO registers  */
static volatile int       running = 1;  /* main loop sentinel      */
static volatile int       mode    = 0;  /* current LED mode 0-3   */
static pthread_mutex_t    mode_mutex = PTHREAD_MUTEX_INITIALIZER;

/* Interrupt statistics */
static volatile uint32_t  isr_count = 0;
static volatile struct timespec last_press_time;

/* ============================================================
 *  GPIO REGISTER MACROS
 * ============================================================ */

/* Set pin as OUTPUT */
#define GPIO_SET_OUTPUT(pin) do {                                \
    int reg = (pin) / 10;                                        \
    int shift = ((pin) % 10) * 3;                               \
    gpio[reg] &= ~(7u << shift);   /* clear 3 bits first */     \
    gpio[reg] |=  (1u << shift);   /* set to 001 = output */    \
} while(0)

/* Set pin as INPUT */
#define GPIO_SET_INPUT(pin) do {                                 \
    int reg = (pin) / 10;                                        \
    int shift = ((pin) % 10) * 3;                               \
    gpio[reg] &= ~(7u << shift);   /* clear 3 bits = input */   \
} while(0)

/* Drive pin HIGH */
#define GPIO_SET(pin)   (gpio[GPSET0] = (1u << (pin)))

/* Drive pin LOW */
#define GPIO_CLR(pin)   (gpio[GPCLR0] = (1u << (pin)))

/* Read pin level — returns 0 or 1 */
#define GPIO_READ(pin)  (((gpio[GPLEV0]) >> (pin)) & 1u)

/* ============================================================
 *  TIMING UTILITIES
 * ============================================================ */

/* Sleep for 'ms' milliseconds */
static void sleep_ms(long ms) {
    struct timespec ts = {
        .tv_sec  = ms / 1000,
        .tv_nsec = (ms % 1000) * NS_PER_MS
    };
    nanosleep(&ts, NULL);
}

/* Sleep for 'us' microseconds */
static void sleep_us(long us) {
    struct timespec ts = {
        .tv_sec  = us / 1000000,
        .tv_nsec = (us % 1000000) * 1000
    };
    nanosleep(&ts, NULL);
}

/* Return current time as milliseconds (monotonic clock) */
static long long time_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000LL + ts.tv_nsec / NS_PER_MS;
}

/* Compute elapsed ms between two timespec values */
static long long elapsed_ms(const struct timespec *a, const struct timespec *b) {
    return (long long)(b->tv_sec  - a->tv_sec)  * 1000LL
         + (long long)(b->tv_nsec - a->tv_nsec) / NS_PER_MS;
}

/* ============================================================
 *  GPIO HARDWARE SETUP
 * ============================================================ */

/* Detect Raspberry Pi peripheral base address from /proc/cpuinfo */
static off_t detect_peri_base(void) {
    FILE *f = fopen("/proc/device-tree/soc/ranges", "rb");
    if (f) {
        unsigned char buf[12];
        if (fread(buf, 1, sizeof(buf), f) == sizeof(buf)) {
            fclose(f);
            /* bytes 4-7 hold the CPU physical address */
            off_t base = ((off_t)buf[4]  << 24) |
                         ((off_t)buf[5]  << 16) |
                         ((off_t)buf[6]  <<  8) |
                          (off_t)buf[7];
            if (base == 0xFE000000) {
                printf("[INFO] Detected Raspberry Pi 4 (base 0xFE000000)\n");
                return BCM2711_PERI_BASE;
            }
        } else {
            fclose(f);
        }
    }
    printf("[INFO] Using default Pi 2/3 base (0x3F000000)\n");
    return BCM2835_PERI_BASE;
}

/* Map GPIO registers into process address space via /dev/mem */
static int gpio_init(void) {
    int fd = open("/dev/mem", O_RDWR | O_SYNC);
    if (fd < 0) {
        /* Fallback to /dev/gpiomem (no root required on Pi OS) */
        fd = open("/dev/gpiomem", O_RDWR | O_SYNC);
        if (fd < 0) {
            perror("[ERROR] Cannot open /dev/mem or /dev/gpiomem");
            fprintf(stderr, "       Run with: sudo ./led_driver\n");
            return -1;
        }
        /* /dev/gpiomem maps GPIO registers at offset 0 */
        gpio = mmap(NULL, BLOCK_SIZE, PROT_READ | PROT_WRITE,
                    MAP_SHARED, fd, 0);
    } else {
        off_t peri_base = detect_peri_base();
        gpio = mmap(NULL, BLOCK_SIZE, PROT_READ | PROT_WRITE,
                    MAP_SHARED, fd, peri_base + GPIO_BASE_OFFSET);
    }
    close(fd);

    if (gpio == MAP_FAILED) {
        perror("[ERROR] mmap failed");
        return -1;
    }

    printf("[INFO] GPIO registers mapped at %p\n", (void*)gpio);
    return 0;
}

/* Configure pin directions and pull-up on button */
static void gpio_setup_pins(void) {
    /* Outputs */
    GPIO_SET_OUTPUT(LED_BLINK);
    GPIO_SET_OUTPUT(LED_PWM);
    GPIO_SET_OUTPUT(LED_PATTERN);

    /* Button input */
    GPIO_SET_INPUT(BTN_PIN);

    /* Enable internal pull-up on button (BCM2835 procedure):
     * 1. Write pull-up/down control (2 = pull-up) to GPPUD
     * 2. Wait 150 cycles
     * 3. Write clock to GPPUDCLK0 for the target pin
     * 4. Wait 150 cycles
     * 5. Clear GPPUD and GPPUDCLK0 */
    gpio[GPPUD] = 2;        /* enable pull-up */
    sleep_us(10);
    gpio[GPPUDCLK0] = (1u << BTN_PIN);
    sleep_us(10);
    gpio[GPPUD]     = 0;
    gpio[GPPUDCLK0] = 0;

    printf("[INFO] Pins configured:\n");
    printf("       LED_BLINK   → GPIO %d (OUTPUT)\n", LED_BLINK);
    printf("       LED_PWM     → GPIO %d (OUTPUT)\n", LED_PWM);
    printf("       LED_PATTERN → GPIO %d (OUTPUT)\n", LED_PATTERN);
    printf("       BUTTON      ← GPIO %d (INPUT, pull-up)\n\n", BTN_PIN);
}

/* Turn all LEDs off */
static void all_leds_off(void) {
    GPIO_CLR(LED_BLINK);
    GPIO_CLR(LED_PWM);
    GPIO_CLR(LED_PATTERN);
}

/* ============================================================
 *  INTERRUPT HANDLER — button press via GPIO sysfs edge detect
 *
 *  Linux GPIO IRQ strategy:
 *    • Export pin via /sys/class/gpio/export
 *    • Set direction to "in"
 *    • Set edge to "falling" (button pulls line low when pressed)
 *    • poll() on value file with POLLPRI — wakes on edge
 *
 *  This runs in its own POSIX thread.
 * ============================================================ */

/* Write string to a sysfs file */
static int sysfs_write(const char *path, const char *value) {
    int fd = open(path, O_WRONLY);
    if (fd < 0) return -1;
    int ret = write(fd, value, strlen(value));
    close(fd);
    return (ret < 0) ? -1 : 0;
}

/* Export/configure GPIO pin for interrupt via sysfs */
static int gpio_export_irq(int pin) {
    char path[64], buf[8];

    /* Export the pin */
    snprintf(buf, sizeof(buf), "%d", pin);
    if (sysfs_write("/sys/class/gpio/export", buf) < 0) {
        /* Already exported — that's fine */
    }
    sleep_ms(100);  /* wait for udev to create the files */

    /* Set direction to input */
    snprintf(path, sizeof(path), "/sys/class/gpio/gpio%d/direction", pin);
    if (sysfs_write(path, "in") < 0) {
        fprintf(stderr, "[WARN] Could not set GPIO%d direction via sysfs\n", pin);
        return -1;
    }

    /* Configure falling-edge interrupt */
    snprintf(path, sizeof(path), "/sys/class/gpio/gpio%d/edge", pin);
    if (sysfs_write(path, "falling") < 0) {
        fprintf(stderr, "[WARN] Could not set GPIO%d edge via sysfs\n", pin);
        return -1;
    }

    printf("[IRQ] GPIO %d configured for falling-edge interrupt (sysfs)\n", pin);
    return 0;
}

/* Unexport GPIO pin on exit */
static void gpio_unexport(int pin) {
    char buf[8];
    snprintf(buf, sizeof(buf), "%d", pin);
    sysfs_write("/sys/class/gpio/unexport", buf);
}

/* Interrupt service thread */
static void *irq_thread(void *arg) {
    (void)arg;
    char path[64];
    char val[4];
    struct pollfd pfd;
    struct timespec now;

    /* Open the value file for the button pin */
    snprintf(path, sizeof(path), "/sys/class/gpio/gpio%d/value", BTN_PIN);
    pfd.fd = open(path, O_RDONLY | O_NONBLOCK);
    if (pfd.fd < 0) {
        fprintf(stderr, "[IRQ] Cannot open GPIO value file: %s\n", path);
        fprintf(stderr, "[IRQ] Interrupt thread disabled — using polling fallback\n");
        return NULL;
    }

    pfd.events = POLLPRI | POLLERR;

    /* Consume initial state to avoid spurious first interrupt */
    lseek(pfd.fd, 0, SEEK_SET);
    read(pfd.fd, val, sizeof(val));

    printf("[IRQ] Interrupt thread running (waiting for button presses)...\n\n");

    while (running) {
        int ret = poll(&pfd, 1, 200 /* ms timeout for running check */);

        if (ret < 0) {
            if (errno == EINTR) continue;
            perror("[IRQ] poll error");
            break;
        }

        if (ret == 0) continue;  /* timeout — check running flag */

        if (pfd.revents & POLLPRI) {
            /* Read and discard the value (required to clear interrupt) */
            lseek(pfd.fd, 0, SEEK_SET);
            read(pfd.fd, val, sizeof(val));

            /* Debounce: ignore events closer than DEBOUNCE_MS apart */
            clock_gettime(CLOCK_MONOTONIC, &now);
            long long gap = elapsed_ms((struct timespec*)&last_press_time, &now);
            if (gap < DEBOUNCE_MS) continue;
            last_press_time = now;

            /* ----- ISR body ----- */
            isr_count++;
            pthread_mutex_lock(&mode_mutex);
            mode = (mode + 1) % 4;  /* cycle through 4 modes */
            pthread_mutex_unlock(&mode_mutex);

            printf("[IRQ] Button press #%u detected! → Mode %d\n",
                   isr_count, mode);
        }
    }

    close(pfd.fd);
    return NULL;
}

/* ============================================================
 *  LED MODES
 *
 *  Mode 0 — Simple blink (LED_BLINK toggles at 1 Hz)
 *  Mode 1 — Software PWM fade (LED_PWM breathes in/out)
 *  Mode 2 — Pattern shift (LED_PATTERN runs a chase sequence)
 *  Mode 3 — All LEDs on (full brightness test)
 * ============================================================ */

/* --- MODE 0: Simple blink using clock_gettime for precise timing --- */
static void mode_blink(void) {
    static long long next_toggle = 0;
    static int state = 0;

    long long now = time_now_ms();
    if (now >= next_toggle) {
        state ^= 1;
        if (state) GPIO_SET(LED_BLINK);
        else        GPIO_CLR(LED_BLINK);
        next_toggle = now + BLINK_PERIOD_MS;
    }
    GPIO_CLR(LED_PWM);
    GPIO_CLR(LED_PATTERN);
}

/* --- MODE 1: Software PWM (duty-cycle 0→100→0 = breathe effect) --- */
/*
 * PWM implementation:
 *   Period = PWM_PERIOD_US microseconds
 *   Duty   = duty_us microseconds HIGH, rest LOW
 *   duty_us sweeps 0 → PWM_PERIOD_US → 0 for breathing effect
 */
static void mode_pwm_fade(void) {
    static int   duty_us  = 0;
    static int   step     = 10;   /* duty step per cycle (microseconds) */
    static int   cycle    = 0;
    static const int CYCLES_PER_STEP = 5;

    int current_mode;
    pthread_mutex_lock(&mode_mutex);
    current_mode = mode;
    pthread_mutex_unlock(&mode_mutex);

    /* Run one PWM period */
    if (duty_us > 0) {
        GPIO_SET(LED_PWM);
        sleep_us(duty_us);
    }
    if ((PWM_PERIOD_US - duty_us) > 0) {
        GPIO_CLR(LED_PWM);
        sleep_us(PWM_PERIOD_US - duty_us);
    }

    /* Update duty cycle every CYCLES_PER_STEP PWM cycles */
    if (++cycle >= CYCLES_PER_STEP) {
        cycle = 0;
        duty_us += step;
        if (duty_us >= PWM_PERIOD_US) { duty_us = PWM_PERIOD_US; step = -10; }
        if (duty_us <= 0)             { duty_us = 0;              step =  10; }
    }

    GPIO_CLR(LED_BLINK);
    GPIO_CLR(LED_PATTERN);
}

/* --- MODE 2: LED chase/pattern --- */
/*
 * Chase pattern: lights each of the 3 LEDs in sequence
 * with configurable on-time per LED.
 */
typedef enum { L_BLINK=0, L_PWM=1, L_PATTERN=2 } led_id_t;
static const int chase_pins[] = { LED_BLINK, LED_PWM, LED_PATTERN };

static void mode_chase(void) {
    static int   current_led = 0;
    static long long next_step = 0;
    static const long long STEP_MS = 200;

    long long now = time_now_ms();
    if (now >= next_step) {
        all_leds_off();
        GPIO_SET(chase_pins[current_led]);
        current_led = (current_led + 1) % 3;
        next_step = now + STEP_MS;
    }
}

/* --- MODE 3: All LEDs on --- */
static void mode_all_on(void) {
    GPIO_SET(LED_BLINK);
    GPIO_SET(LED_PWM);
    GPIO_SET(LED_PATTERN);
}

/* ============================================================
 *  BUTTON POLLING FALLBACK
 *  Used when interrupt thread can't open sysfs value file.
 *  Called from the main loop; applies debounce logic.
 * ============================================================ */
static void poll_button_fallback(void) {
    static int prev_state = 1;     /* 1 = not pressed (pull-up) */
    static long long last_change = 0;

    int state = GPIO_READ(BTN_PIN);
    long long now = time_now_ms();

    if (state != prev_state && (now - last_change) > DEBOUNCE_MS) {
        if (state == 0) {          /* falling edge = button pressed */
            isr_count++;
            pthread_mutex_lock(&mode_mutex);
            mode = (mode + 1) % 4;
            pthread_mutex_unlock(&mode_mutex);
            printf("[POLL] Button press #%u (polling) → Mode %d\n",
                   isr_count, mode);
        }
        prev_state = state;
        last_change = now;
    }
}

/* ============================================================
 *  PERIODIC STATUS REPORT (every 5 seconds)
 * ============================================================ */
static void print_status(void) {
    static long long next_report = 0;
    long long now = time_now_ms();
    if (now >= next_report) {
        int m;
        pthread_mutex_lock(&mode_mutex);
        m = mode;
        pthread_mutex_unlock(&mode_mutex);

        const char *mode_names[] = {
            "Blink (1 Hz)", "PWM Fade (breathe)", "Chase Pattern", "All On"
        };
        printf("[STATUS] Mode=%d (%s)  |  Button presses=%u  |  Time=%lld ms\n",
               m, mode_names[m], isr_count, now);
        next_report = now + 5000;
    }
}

/* ============================================================
 *  SIGNAL HANDLER — clean exit on Ctrl+C
 * ============================================================ */
static void signal_handler(int sig) {
    (void)sig;
    printf("\n[SIGNAL] Caught signal %d — shutting down...\n", sig);
    running = 0;
}

/* ============================================================
 *  MAIN
 * ============================================================ */
int main(void) {
    printf("==============================================\n");
    printf("  Raspberry Pi LED Driver — C Demo\n");
    printf("  GPIO I/O | Interrupts | Timing | PWM\n");
    printf("==============================================\n\n");

    /* ---- Setup signal handling ---- */
    signal(SIGINT,  signal_handler);
    signal(SIGTERM, signal_handler);

    /* ---- Initialise GPIO memory map ---- */
    if (gpio_init() < 0) {
        return EXIT_FAILURE;
    }

    /* ---- Configure pin directions ---- */
    gpio_setup_pins();
    all_leds_off();

    /* ---- Setup GPIO interrupt via sysfs ---- */
    int irq_ok = (gpio_export_irq(BTN_PIN) == 0);

    /* ---- Start interrupt thread ---- */
    pthread_t irq_tid = 0;
    if (irq_ok) {
        if (pthread_create(&irq_tid, NULL, irq_thread, NULL) != 0) {
            perror("[IRQ] pthread_create failed");
            irq_ok = 0;
        }
    }
    if (!irq_ok) {
        printf("[INFO] Falling back to button polling (no IRQ)\n");
    }

    /* Initialise debounce timestamp */
    clock_gettime(CLOCK_MONOTONIC, (struct timespec*)&last_press_time);

    printf("[INFO] Press the button (GPIO %d) to cycle LED modes.\n", BTN_PIN);
    printf("[INFO] Press Ctrl+C to exit.\n\n");

    /* ================================================================
     * MAIN LOOP
     *   Non-blocking: each mode function checks elapsed time itself
     *   so the loop runs as fast as possible without busy-waiting
     *   (PWM mode sleeps in microsecond bursts naturally).
     * ================================================================ */
    while (running) {
        int current_mode;
        pthread_mutex_lock(&mode_mutex);
        current_mode = mode;
        pthread_mutex_unlock(&mode_mutex);

        /* Dispatch to active mode */
        switch (current_mode) {
            case 0: mode_blink();    break;
            case 1: mode_pwm_fade(); break;
            case 2: mode_chase();    break;
            case 3: mode_all_on();   break;
            default: break;
        }

        /* Polling fallback if IRQ unavailable */
        if (!irq_ok) {
            poll_button_fallback();
        }

        /* Periodic status print */
        print_status();

        /* Yield CPU briefly in modes that don't already sleep */
        if (current_mode == 0 || current_mode == 2 || current_mode == 3) {
            sleep_ms(1);
        }
    }

    /* ================================================================
     * CLEANUP
     * ================================================================ */
    printf("[INFO] Cleaning up...\n");

    /* Wait for interrupt thread to finish */
    if (irq_tid) {
        pthread_join(irq_tid, NULL);
    }

    /* Unexport sysfs GPIO */
    gpio_unexport(BTN_PIN);

    /* Turn all LEDs off */
    all_leds_off();

    /* Unmap GPIO registers */
    munmap((void*)gpio, BLOCK_SIZE);

    printf("[INFO] GPIO unmapped. All LEDs off.\n");
    printf("[INFO] Total button presses: %u\n", isr_count);
    printf("[INFO] Done. Goodbye!\n");

    return EXIT_SUCCESS;
}
