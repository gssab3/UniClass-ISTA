package it.unisa.uniclass.testing.unit.conversazioni.model;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.utenti.model.Accademico;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test unitario per la classe Messaggio (Entity).
 * Copertura: 100% (incluso il metodo privato/protetto @PrePersist)
 */
class MessaggioTest {

    @Test
    @DisplayName("Test Costruttore Vuoto e Setter/Getter")
    void testNoArgsConstructorAndSetters() {
        Messaggio m = new Messaggio();

        Accademico autore = new Accademico(); autore.setMatricola("111");
        Accademico destinatario = new Accademico(); destinatario.setMatricola("222");
        Topic topic = new Topic(); topic.setNome("Tesi");
        String body = "Ciao Prof";
        LocalDateTime now = LocalDateTime.now();

        m.setAutore(autore);
        m.setDestinatario(destinatario);
        m.setTopic(topic);
        m.setBody(body);
        m.setDateTime(now);

        assertAll("Verifica proprietà",
                () -> assertSame(autore, m.getAutore()),
                () -> assertSame(destinatario, m.getDestinatario()),
                () -> assertSame(topic, m.getTopic()),
                () -> assertEquals(body, m.getBody()),
                () -> assertEquals(now, m.getDateTime()),
                () -> assertNull(m.getId()) // ID è null prima della persistenza
        );
    }

    @Test
    @DisplayName("Test Costruttore Parametrico")
    void testAllArgsConstructor() {
        Accademico autore = new Accademico();
        Accademico dest = new Accademico();
        Topic topic = new Topic();
        String body = "Body";
        LocalDateTime dt = LocalDateTime.now();

        Messaggio m = new Messaggio(autore, dest, topic, body, dt);

        assertAll(
                () -> assertSame(autore, m.getAutore()),
                () -> assertSame(dest, m.getDestinatario()),
                () -> assertSame(topic, m.getTopic()),
                () -> assertEquals(body, m.getBody()),
                () -> assertEquals(dt, m.getDateTime())
        );
    }

    @Test
    @DisplayName("Test @PrePersist onCreate")
    void testPrePersist() throws Exception {
        Messaggio m = new Messaggio();
        assertNull(m.getDateTime());

        // Simuliamo la chiamata di JPA via Reflection perché il metodo è protected
        Method method = Messaggio.class.getDeclaredMethod("onCreate");
        method.setAccessible(true);
        method.invoke(m);

        assertNotNull(m.getDateTime(), "La data dovrebbe essere settata dopo onCreate");

        // Verifica che se la data esiste già, non venga sovrascritta
        LocalDateTime oldDate = LocalDateTime.of(2020, 1, 1, 10, 0);
        m.setDateTime(oldDate);
        method.invoke(m);
        assertEquals(oldDate, m.getDateTime(), "La data esistente non deve cambiare");
    }

    @Test
    @DisplayName("Test toString")
    void testToString() {
        Messaggio m = new Messaggio();
        m.setBody("Test Body");

        String result = m.toString();

        assertNotNull(result);
        assertTrue(result.contains("Test Body"));
        assertTrue(result.contains("Messaggio{"));
    }
}