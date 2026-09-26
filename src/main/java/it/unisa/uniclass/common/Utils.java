package it.unisa.uniclass.common;

public class Utils {
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
