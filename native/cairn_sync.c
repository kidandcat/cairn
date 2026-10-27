#define _POSIX_C_SOURCE 200809L

/*
Minimal durability shim for the native file backend.

Lean 4.35 has no fsync. This file is the only C in cairn. The pure core
never calls it. On Linux the data barrier is fdatasync; the directory
barrier is fsync. On macOS both go through F_FULLFSYNC, which asks the
drive to flush its own cache, and fall back to fsync if that fails.

A successful return means the OS accepted the barrier. Disks that lie
about flush completion are outside what this shim can see.
*/
#include <errno.h>
#include <fcntl.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

#if defined(__APPLE__)
#include <sys/stat.h>
#endif

static lean_obj_res cairn_err(const char *what) {
    int err = errno;
    char buf[160];
    const char *msg = strerror(err);
    if (msg == 0) {
        msg = "unknown";
    }
    snprintf(buf, sizeof(buf), "%s: %s", what, msg);
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

static int cairn_data_sync(int fd) {
#if defined(__APPLE__)
    if (fcntl(fd, F_FULLFSYNC) == 0) {
        return 0;
    }
    return fsync(fd);
#else
    return fdatasync(fd);
#endif
}

static int cairn_meta_sync(int fd) {
#if defined(__APPLE__)
    if (fcntl(fd, F_FULLFSYNC) == 0) {
        return 0;
    }
    return fsync(fd);
#else
    return fsync(fd);
#endif
}

LEAN_EXPORT lean_obj_res cairn_open_append(b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    int fd = open(lean_string_cstr(path), O_RDWR | O_CREAT | O_APPEND, 0644);
    if (fd < 0) {
        return cairn_err("open append");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res cairn_open_trunc(b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    int fd = open(lean_string_cstr(path), O_RDWR | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) {
        return cairn_err("open trunc");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res cairn_write(uint32_t fd, b_lean_obj_arg buf, lean_obj_arg world) {
    (void)world;
    size_t n = lean_sarray_size(buf);
    const uint8_t *p = lean_sarray_cptr(buf);
    size_t off = 0;
    while (off < n) {
        ssize_t k = write((int)fd, p + off, n - off);
        if (k < 0) {
            if (errno == EINTR) {
                continue;
            }
            return cairn_err("write");
        }
        if (k == 0) {
            return cairn_err("write: short");
        }
        off += (size_t)k;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res cairn_datasync(uint32_t fd, lean_obj_arg world) {
    (void)world;
    if (cairn_data_sync((int)fd) != 0) {
        return cairn_err("datasync");
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res cairn_close_fd(uint32_t fd, lean_obj_arg world) {
    (void)world;
    if (close((int)fd) != 0) {
        return cairn_err("close");
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* fsync the parent directory of `path` so a create or rename survives power loss. */
LEAN_EXPORT lean_obj_res cairn_sync_dir(b_lean_obj_arg path, lean_obj_arg world) {
    (void)world;
    const char *s = lean_string_cstr(path);
    size_t n = strlen(s);
    char stack[4096];
    if (n >= sizeof(stack)) {
        return cairn_err("sync dir: path too long");
    }
    memcpy(stack, s, n + 1);
    char *slash = strrchr(stack, '/');
    const char *dir = ".";
    if (slash != 0) {
        if (slash == stack) {
            dir = "/";
        } else {
            *slash = 0;
            dir = stack;
        }
    }
    int fd = open(dir, O_RDONLY | O_DIRECTORY);
    if (fd < 0) {
        return cairn_err("open dir");
    }
    int rc = cairn_meta_sync(fd);
    int saved = errno;
    close(fd);
    if (rc != 0) {
        errno = saved;
        return cairn_err("fsync dir");
    }
    return lean_io_result_mk_ok(lean_box(0));
}
