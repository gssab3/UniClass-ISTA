package it.unisa.uniclass.common;

public class Utils {
    private static final java.util.regex.Pattern EMAIL =
            java.util.regex.Pattern.compile("^[a-zA-Z0-9._%+-]+@(studenti\\.unisa\\.it|unisa\\.it)$");
    private static final java.util.regex.Pattern MAT =
            java.util.regex.Pattern.compile("^\\d{10}$");

    public static boolean isEmail(String v) {
        return v != null && EMAIL.matcher(v).matches();
    }

    public static boolean isMatricola(String v) {
        return v != null && MAT.matcher(v).matches();
    }

    public static boolean isTestoMsg(String v) {
        return v != null && !v.isBlank() && v.length() <= 2000;
    }

    public static String escapeHTML(String value) {
        if(value == null)
            return "";

        return value
                .replace("&", "&amp;")
                .replace("<", "&lt;")
                .replace(">", "&gt;")
                .replace("\"", "&quot;")
                .replace("'", "&#39;");
    }
}
