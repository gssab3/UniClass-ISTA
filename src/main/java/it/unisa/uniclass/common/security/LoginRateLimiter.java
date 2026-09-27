package it.unisa.uniclass.common.security;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.concurrent.ConcurrentHashMap;

public class LoginRateLimiter {
    private static final int MAX_ATTEMPTS = 5;
    private static final long WINDOW_MS = 900000;
    private static final long BLOCK_MS = 900000;
    private static final ConcurrentHashMap<String, Attempt> ATTEMPTS = new ConcurrentHashMap<>();

    private static class Attempt {
        private final Deque<Long> failures = new ArrayDeque<>();
        private long blockedUntil = 0;
    }

    public static String key(String ip, String email) {
        String cleanIp = ip == null ? "unknown" : ip;
        String cleanEmail = email == null ? "unknown" : email.trim().toLowerCase();
        return cleanIp + "|" + cleanEmail;
    }

    public static boolean isBlocked(String key) {
        Attempt attempt = ATTEMPTS.get(key);
        if (attempt == null) {
            return false;
        }
        synchronized (attempt) {
            long now = System.currentTimeMillis();
            if (attempt.blockedUntil > now) {
                return true;
            }
            while (!attempt.failures.isEmpty() && now - attempt.failures.peekFirst() > WINDOW_MS) {
                attempt.failures.pollFirst();
            }
            if (attempt.failures.size() >= MAX_ATTEMPTS) {
                attempt.blockedUntil = now + BLOCK_MS;
                return true;
            }
            return false;
        }
    }

    public static void recordFailure(String key) {
        Attempt attempt = ATTEMPTS.computeIfAbsent(key, k -> new Attempt());
        synchronized (attempt) {
            long now = System.currentTimeMillis();
            while (!attempt.failures.isEmpty() && now - attempt.failures.peekFirst() > WINDOW_MS) {
                attempt.failures.pollFirst();
            }
            attempt.failures.addLast(now);
            if (attempt.failures.size() >= MAX_ATTEMPTS) {
                attempt.blockedUntil = now + BLOCK_MS;
            }
        }
    }

    public static void reset(String key) {
        ATTEMPTS.remove(key);
    }
}
