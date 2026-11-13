/*
 * cet_profile.h -- the harnesses' check of the supported profile.
 *
 * tisa_drive and tisa_records enter their callees with `call enter;
 * enter: push r15; ret`, which faults under user-mode shadow stacks (CET
 * SHSTK). cet_profile prints the process's CET state as the kernel reports
 * it (the x86_Thread_features lines of /proc/self/status) and returns true
 * when shadow stacks are off.
 */
#pragma once

#include <stdbool.h>
#include <stdio.h>
#include <string.h>

static bool cet_profile(void) {
    FILE *f = fopen("/proc/self/status", "r");
    char line[256];
    bool seen = false, shstk = false;
    if (f) {
        while (fgets(line, sizeof line, f)) {
            if (strncmp(line, "x86_Thread_features", 19)) continue;
            seen = true;
            line[strcspn(line, "\n")] = 0;
            printf("cet: %s\n", line);
            if (!strncmp(line, "x86_Thread_features:", 20) && strstr(line + 20, "shstk")) shstk = true;
        }
        fclose(f);
    }
    if (!seen) printf("cet: no x86_Thread_features in /proc/self/status (a kernel without user shadow stacks)\n");
    printf("cet: shadow stack (SHSTK) %s; the supported profile needs it off\n", shstk ? "ON" : "off");
    return !shstk;
}
