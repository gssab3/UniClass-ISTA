package it.unisa.uniclass.common.security;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Set;
import java.util.stream.Collectors;

public final class CommonPasswordListBlocker {
    private static final Set<String> commonPasswords = load();

    private static Set<String> load() {
        try (InputStream input =
                     CommonPasswordListBlocker.class
                             .getResourceAsStream("/top_3000_passwords.txt")) {

            if (input == null) {
                throw new IllegalStateException("Password list not found");
            }

            return new String(input.readAllBytes(), StandardCharsets.UTF_8)
                    .lines()
                    .map(String::trim)
                    .filter(line -> !line.isEmpty())
                    .collect(Collectors.toUnmodifiableSet());

        } catch (IOException e) {
            throw new IllegalStateException("Could not load password list", e);
        }
    }

    public static boolean isCommon(String password) {
        return commonPasswords.contains(password);
    }
}
