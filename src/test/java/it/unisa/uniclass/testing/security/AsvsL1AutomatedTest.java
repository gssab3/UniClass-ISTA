package it.unisa.uniclass.testing.security;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import javax.net.ssl.HttpsURLConnection;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.time.Duration;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Acceptance test black-box AUTOMATIZZATI per ASVS L1 v5 (RAD UniClass v2.0).
 * Avvia l'app e spostati su /Home per poi effettuare questo test.
 * Puoi eventualmente eseguire mvn -Dtest=AsvsL1AutomatedTest test.
 * Contiene SOLO i requisiti completamente automatizzabili
 * deterministico via HTTP/TLS, senza stato applicativo, senza autenticazione,
 * senza giudizio umano, senza code review e senza lettura di documentazione.
 * Tutti gli altri requisiti sono in ASVS_L1_ManualChecklist.md (nessun overlap).
 * Requisiti coperti qui (9): 3.3.1, 3.4.1, 3.4.2, 4.1.1, 6.2.6, 12.1.1, 12.2.1, 12.2.2, 13.4.1.
 */
@DisplayName("ASVS L1 - Automated (black-box, no-auth, read-only)")
class AsvsL1AutomatedTest {

    private static final String BASE_URL = "http://localhost:8080/UniClass-Dependability";

    // "evil.example" è un dominio RISERVATO (RFC 2606) che non esiste
    private static final String EVIL_ORIGIN = "https://evil.example";

    private static final HttpClient CLIENT = HttpClient.newBuilder()
            .connectTimeout(Duration.ofSeconds(5))
            .followRedirects(HttpClient.Redirect.NEVER)
            .build();

    // ---------- helpers ----------

    private static HttpResponse<String> get(String path, Map<String, String> headers) throws Exception {
        String url = BASE_URL.endsWith("/") && path.startsWith("/")
                ? BASE_URL.substring(0, BASE_URL.length() - 1) + path
                : BASE_URL + (path.startsWith("/") ? path : "/" + path);
        HttpRequest.Builder b = HttpRequest.newBuilder(URI.create(url)).GET()
                .timeout(Duration.ofSeconds(5));
        if (headers != null) headers.forEach(b::header);
        try {
            return CLIENT.send(b.build(), HttpResponse.BodyHandlers.ofString());
        } catch (java.net.ConnectException e) {
            fail("App non raggiungibile su " + BASE_URL + " — avviala prima con 'docker compose up'. "
                    + "Se gira su un altro indirizzo, correggi la costante BASE_URL in cima a questo file. "
                    + "Dettaglio: " + e.getMessage());
            throw e; // mai raggiunto
        }
    }

    private static Optional<String> header(HttpResponse<?> r, String name) {
        return r.headers().firstValue(name);
    }

    private static String norm(String s) {
        return s == null ? "" : s.trim();
    }

    // ---------- 3.3.1 Secure cookie ----------

    @Test
    @DisplayName("3.3.1 - Cookie di sessione con attributo Secure")
    void asvs331_SecureCookieFlag() throws Exception {
        HttpResponse<String> r = get("/Home", null);
        List<String> setCookies = r.headers().allValues("set-cookie");
        if (setCookies.isEmpty()) {
            // Fallback: la sessione potrebbe essere creata su Login.jsp
            setCookies = get("/Login.jsp", null).headers().allValues("set-cookie");
        }
        assertFalse(setCookies.isEmpty(),
                "FAIL 3.3.1: nessuna header Set-Cookie osservata su /Home né /Login.jsp, impossibile verificare Secure.");
        for (String c : setCookies) {
            String lower = c.toLowerCase();
            if (lower.startsWith("jsessionid") || lower.contains("session")) {
                assertTrue(lower.contains("secure"),
                        "FAIL 3.3.1: cookie di sessione senza flag Secure: " + c);
            }
        }
    }

    // ---------- 3.4.1 HSTS ----------

    @Test
    @DisplayName("3.4.1 - Strict-Transport-Security su tutte le risposte")
    void asvs341_HstsHeader() throws Exception {
        HttpResponse<String> r = get("/Home", null);
        String hsts = norm(header(r, "strict-transport-security").orElse(""));
        assertFalse(hsts.isEmpty(), "FAIL 3.4.1: header Strict-Transport-Security assente.");
        assertTrue(hsts.toLowerCase().contains("max-age"),
                "FAIL 3.4.1: HSTS senza max-age: " + hsts);
        long maxAge = Long.parseLong(hsts.replaceAll("(?i).*max-age\\s*=\\s*(\\d+).*", "$1"));
        assertTrue(maxAge >= 31536000,
                "FAIL 3.4.1: max-age < 1 anno: " + maxAge);
    }

    // ---------- 3.4.2 CORS ----------

    @Test
    @DisplayName("3.4.2 - Access-Control-Allow-Origin non riflesso / non wildcard con dati sensibili")
    void asvs342_CorsFixedOrigin() throws Exception {
        // NON MODIFICARE l'Origin qui sotto: deve restare un sito esterno mai autorizzato.
        HttpResponse<String> r = get("/Home", Map.of("Origin", EVIL_ORIGIN));
        Optional<String> acao = header(r, "access-control-allow-origin");
        if (acao.isEmpty()) {
            return; // Nessun CORS esposto -> PASS
        }
        String v = norm(acao.get());
        assertNotEquals(EVIL_ORIGIN, v,
                "FAIL 3.4.2: Origin non in allowlist viene riflesso.");
        if ("*".equals(v)) {
            // Wildcard tollerata solo se la risposta non contiene dati sensibili / sessione
            List<String> cookies = r.headers().allValues("set-cookie");
            assertTrue(cookies.isEmpty(),
                    "FAIL 3.4.2: ACAO=* con Set-Cookie nella stessa risposta.");
        }
    }

    // ---------- 4.1.1 Content-Type + charset ----------

    @Test
    @DisplayName("4.1.1 - Content-Type con charset sicuro su risposte HTML")
    void asvs411_ContentTypeCharset() throws Exception {
        for (String path : List.of("/Home", "/Login.jsp")) {
            HttpResponse<String> r = get(path, null);
            String ct = norm(header(r, "content-type").orElse("")).toLowerCase();
            assertFalse(ct.isEmpty(), "FAIL 4.1.1: Content-Type assente su " + path);
            assertTrue(ct.contains("charset="), "FAIL 4.1.1: charset assente in Content-Type su " + path + ": " + ct);
            assertTrue(ct.contains("utf-8") || ct.contains("iso-8859-1"),
                    "FAIL 4.1.1: charset non sicuro su " + path + ": " + ct);
        }
    }

    // ---------- 6.2.6 password masking ----------

    @Test
    @DisplayName("6.2.6 - Campo password con type=password")
    void asvs626_PasswordInputMasked() throws Exception {
        HttpResponse<String> r = get("/Login.jsp", null);
        String body = r.body() == null ? "" : r.body().toLowerCase();
        assertTrue(body.contains("name=\"password\"") || body.contains("name='password'") || body.contains("id=\"password\""),
                "FAIL 6.2.6: campo password non trovato in Login.jsp.");
        assertTrue(body.contains("type=\"password\"") || body.contains("type='password'"),
                "FAIL 6.2.6: input password senza type=password in Login.jsp.");
    }

    // ---------- 12.2.1 TLS enforcement ----------

    @Test
    @DisplayName("12.2.1 - HTTP non deve servire contenuti senza redirect a HTTPS")
    void asvs1221_TlsEnforced() throws Exception {
        HttpResponse<String> r = get("/Home", null);
        int status = r.statusCode();
        assertTrue(status == 301 || status == 302 || status == 307 || status == 308,
                "FAIL 12.2.1: GET http non redirige a HTTPS (status=" + status + ").");
        String loc = norm(header(r, "location").orElse(""));
        assertTrue(loc.toLowerCase().startsWith("https://"),
                "FAIL 12.2.1: redirect Location non HTTPS: " + loc);
    }

    // ---------- 12.1.1 / 12.2.2 TLS version + trusted cert ----------
    // NON MODIFICARE: l'URL https è derivato da BASE_URL (8080 -> 8443, default TomEE).

    private static String tlsBaseUrl() {
        // Deriva https da BASE_URL: 8080 -> 8443 per TomEE locale
        String https = BASE_URL.replaceFirst("^http:", "https:");
        if (https.equals(BASE_URL)) https = BASE_URL; // era gia' https
        https = https.replace(":8080", ":8443");
        return https;
    }

    @Test
    @DisplayName("12.1.1 - Solo TLS 1.2/1.3 abilitati")
    void asvs1211_TlsVersions() throws Exception {
        URI u = URI.create(tlsBaseUrl() + "/Home");
        String host = u.getHost();
        int port = u.getPort() == -1 ? 443 : u.getPort();
        javax.net.ssl.SSLSocketFactory factory =
                (javax.net.ssl.SSLSocketFactory) javax.net.ssl.SSLSocketFactory.getDefault();
        try (javax.net.ssl.SSLSocket s = (javax.net.ssl.SSLSocket) factory.createSocket(host, port)) {
            s.setSoTimeout(5000);
            s.setEnabledProtocols(new String[]{"TLSv1.2", "TLSv1.3"});
            s.startHandshake();
            String protocol = s.getSession().getProtocol();
            assertTrue(protocol.equals("TLSv1.2") || protocol.equals("TLSv1.3"),
                    "FAIL 12.1.1: protocollo negoziato non consentito: " + protocol);
        } catch (Exception e) {
            fail("FAIL 12.1.1: handshake TLS 1.2/1.3 fallito verso " + host + ":" + port + ": " + e.getMessage());
        }
    }

    @Test
    @DisplayName("12.2.2 - Certificato TLS pubblicamente trusted")
    void asvs1222_TrustedCertificate() throws Exception {
        HttpsURLConnection c = null;
        try {
            c = (HttpsURLConnection) URI.create(tlsBaseUrl() + "/Home").toURL().openConnection();
            c.setConnectTimeout(5000);
            c.setReadTimeout(5000);
            c.connect(); // TrustManager di default: fallisce se self-signed / non trusted
            assertNotNull(c.getServerCertificates(),
                    "FAIL 12.2.2: nessuna catena di certificati presentata.");
        } catch (ClassCastException e) {
            fail("FAIL 12.2.2: endpoint TLS non disponibile: " + tlsBaseUrl());
        } catch (Exception e) {
            fail("FAIL 12.2.2: certificato non trusted o handshake fallito: " + e.getMessage());
        } finally {
            if (c != null) c.disconnect();
        }
    }

    // ---------- 13.4.1 source control metadata ----------

    @Test
    @DisplayName("13.4.1 - Nessun metadata source-control esposto")
    void asvs1341_NoSourceControlExposure() throws Exception {
        for (String path : List.of("/.git/HEAD", "/.svn/entries", "/WEB-INF/web.xml", "/.env")) {
            HttpResponse<String> r = get(path, null);
            int s = r.statusCode();
            assertTrue(s == 404 || s == 403,
                    "FAIL 13.4.1: " + path + " esposto (status=" + s + ").");
            String body = r.body() == null ? "" : r.body();
            assertFalse(body.contains("[core]") && body.contains("ref: refs/"),
                    "FAIL 13.4.1: contenuto .git/HEAD trapelato.");
        }
    }
}
