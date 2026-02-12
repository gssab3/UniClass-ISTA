package it.unisa.uniclass.testing.unit.conversazioni.model;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Test completi per la classe Messaggio.
 * Coverage massimizzata per JaCoCo: getter, setter, costruttori, toString.
 */
public class MessaggioTest {

    private Messaggio messaggio;
    private Accademico autore;
    private Accademico destinatario;
    private Topic topic;
    private LocalDateTime dateTime;
    private CorsoLaurea corsoLaurea;

    @BeforeEach
    public void setUp() {
        // Setup CorsoLaurea
        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        // Setup Autore (Studente)
        autore = new Studente();
        autore.setEmail("studente@studenti.unisa.it");
        autore.setNome("Mario");
        autore.setCognome("Rossi");
        autore.setMatricola("0512100001");
        autore.setCorsoLaurea(corsoLaurea);

        // Setup Destinatario (Docente)
        destinatario = new Docente();
        destinatario.setEmail("docente@unisa.it");
        destinatario.setNome("Luigi");
        destinatario.setCognome("Verdi");
        destinatario.setMatricola("0512100999");
        destinatario.setCorsoLaurea(corsoLaurea);

        // Setup Topic
        topic = new Topic();
        topic.setNome("Esame");
        topic.setCorsoLaurea(corsoLaurea);

        // Setup DateTime
        dateTime = LocalDateTime.now();

        // Crea messaggio con costruttore vuoto
        messaggio = new Messaggio();
    }

    @Test
    public void testCostruttoreVuoto() {
        System.out.println("\n=== Test 1: Costruttore vuoto ===");

        Messaggio msg = new Messaggio();

        assertNotNull(msg);
        assertNull(msg.getId());
        assertNull(msg.getAutore());
        assertNull(msg.getDestinatario());
        assertNull(msg.getBody());
        assertNull(msg.getDateTime());
        assertNull(msg.getTopic());

        System.out.println("✓ Costruttore vuoto testato correttamente");
    }

    @Test
    public void testCostruttoreCompleto() {
        System.out.println("\n=== Test 2: Costruttore completo ===");

        String body = "Questo è un messaggio di test";
        Messaggio msg = new Messaggio(autore, destinatario, topic, body, dateTime);

        assertNotNull(msg);
        assertEquals(autore, msg.getAutore());
        assertEquals(destinatario, msg.getDestinatario());
        assertEquals(topic, msg.getTopic());
        assertEquals(body, msg.getBody());
        assertEquals(dateTime, msg.getDateTime());

        System.out.println("✓ Costruttore completo testato: tutti i campi inizializzati correttamente");
    }

    @Test
    public void testCostruttoreCompletoConTopicNull() {
        System.out.println("\n=== Test 3: Costruttore completo con topic null ===");

        String body = "Messaggio senza topic";
        Messaggio msg = new Messaggio(autore, destinatario, null, body, dateTime);

        assertNotNull(msg);
        assertEquals(autore, msg.getAutore());
        assertEquals(destinatario, msg.getDestinatario());
        assertNull(msg.getTopic());
        assertEquals(body, msg.getBody());
        assertEquals(dateTime, msg.getDateTime());

        System.out.println("✓ Costruttore con topic null testato correttamente");
    }

    @Test
    public void testGetSetAutore() {
        System.out.println("\n=== Test 4: Get/Set Autore ===");

        assertNull(messaggio.getAutore());

        messaggio.setAutore(autore);

        assertEquals(autore, messaggio.getAutore());
        assertEquals("Mario", messaggio.getAutore().getNome());
        assertEquals("Rossi", messaggio.getAutore().getCognome());

        System.out.println("✓ Getter e Setter di Autore funzionano correttamente");
    }

    @Test
    public void testGetSetDestinatario() {
        System.out.println("\n=== Test 5: Get/Set Destinatario ===");

        assertNull(messaggio.getDestinatario());

        messaggio.setDestinatario(destinatario);

        assertEquals(destinatario, messaggio.getDestinatario());
        assertEquals("Luigi", messaggio.getDestinatario().getNome());
        assertEquals("Verdi", messaggio.getDestinatario().getCognome());

        System.out.println("✓ Getter e Setter di Destinatario funzionano correttamente");
    }

    @Test
    public void testGetSetBody() {
        System.out.println("\n=== Test 6: Get/Set Body ===");

        assertNull(messaggio.getBody());

        String body = "Ciao, come va?";
        messaggio.setBody(body);

        assertEquals(body, messaggio.getBody());

        System.out.println("✓ Getter e Setter di Body funzionano correttamente");
    }

    @Test
    public void testGetSetBodyVuoto() {
        System.out.println("\n=== Test 7: Get/Set Body vuoto ===");

        messaggio.setBody("");

        assertEquals("", messaggio.getBody());
        assertTrue(messaggio.getBody().isEmpty());

        System.out.println("✓ Body vuoto gestito correttamente");
    }

    @Test
    public void testGetSetBodyLungo() {
        System.out.println("\n=== Test 8: Get/Set Body lungo ===");

        String longBody = "Lorem ipsum dolor sit amet. ".repeat(100);
        messaggio.setBody(longBody);

        assertEquals(longBody, messaggio.getBody());
        assertTrue(messaggio.getBody().length() > 1000);

        System.out.println("✓ Body lungo (" + longBody.length() + " caratteri) gestito correttamente");
    }

    @Test
    public void testGetSetBodyConCaratteriSpeciali() {
        System.out.println("\n=== Test 9: Get/Set Body con caratteri speciali ===");

        String specialBody = "àèéìòù €£$¥ @#&*() <>'\" 你好 🚀 \n\t\r";
        messaggio.setBody(specialBody);

        assertEquals(specialBody, messaggio.getBody());

        System.out.println("✓ Body con caratteri speciali gestito correttamente");
    }

    @Test
    public void testGetSetDateTime() {
        System.out.println("\n=== Test 10: Get/Set DateTime ===");

        assertNull(messaggio.getDateTime());

        LocalDateTime now = LocalDateTime.now();
        messaggio.setDateTime(now);

        assertEquals(now, messaggio.getDateTime());

        System.out.println("✓ Getter e Setter di DateTime funzionano correttamente");
    }

    @Test
    public void testGetSetDateTimeDifferenti() {
        System.out.println("\n=== Test 11: Get/Set DateTime con date diverse ===");

        LocalDateTime past = LocalDateTime.of(2020, 1, 1, 10, 30);
        messaggio.setDateTime(past);
        assertEquals(past, messaggio.getDateTime());

        LocalDateTime future = LocalDateTime.of(2030, 12, 31, 23, 59);
        messaggio.setDateTime(future);
        assertEquals(future, messaggio.getDateTime());

        System.out.println("✓ DateTime con date diverse gestito correttamente");
    }

    @Test
    public void testGetSetTopic() {
        System.out.println("\n=== Test 12: Get/Set Topic ===");

        assertNull(messaggio.getTopic());

        messaggio.setTopic(topic);

        assertEquals(topic, messaggio.getTopic());
        assertEquals("Esame", messaggio.getTopic().getNome());

        System.out.println("✓ Getter e Setter di Topic funzionano correttamente");
    }

    @Test
    public void testGetSetTopicNull() {
        System.out.println("\n=== Test 13: Get/Set Topic null ===");

        messaggio.setTopic(topic);
        assertNotNull(messaggio.getTopic());

        messaggio.setTopic(null);
        assertNull(messaggio.getTopic());

        System.out.println("✓ Topic null gestito correttamente");
    }

    @Test
    public void testGetIdNonImpostato() {
        System.out.println("\n=== Test 14: Get ID non impostato ===");

        assertNull(messaggio.getId());

        System.out.println("✓ ID null (non impostato) gestito correttamente");
    }

    @Test
    public void testToStringConTuttiICampi() {
        System.out.println("\n=== Test 15: ToString con tutti i campi ===");

        messaggio.setAutore(autore);
        messaggio.setDestinatario(destinatario);
        messaggio.setBody("Test body");
        messaggio.setDateTime(dateTime);
        messaggio.setTopic(topic);

        String result = messaggio.toString();

        assertNotNull(result);
        assertTrue(result.contains("Messaggio{"));
        assertTrue(result.contains("id="));
        assertTrue(result.contains("body='Test body'"));
        assertTrue(result.contains("topic="));
        assertTrue(result.contains("dateTime="));
        assertTrue(result.contains("autore="));
        assertTrue(result.contains("destinatario="));

        System.out.println("✓ ToString: " + result.substring(0, Math.min(100, result.length())) + "...");
    }

    @Test
    public void testToStringConCampiVuoti() {
        System.out.println("\n=== Test 16: ToString con campi vuoti ===");

        String result = messaggio.toString();

        assertNotNull(result);
        assertTrue(result.contains("Messaggio{"));
        assertTrue(result.contains("id=null"));
        assertTrue(result.contains("body='null'"));

        System.out.println("✓ ToString con campi null gestito correttamente");
    }

    @Test
    public void testToStringConBodyVuoto() {
        System.out.println("\n=== Test 17: ToString con body vuoto ===");

        messaggio.setBody("");
        messaggio.setAutore(autore);
        messaggio.setDestinatario(destinatario);

        String result = messaggio.toString();

        assertNotNull(result);
        assertTrue(result.contains("body=''"));

        System.out.println("✓ ToString con body vuoto: " + result.substring(0, Math.min(80, result.length())));
    }

    @Test
    public void testMessaggioCompleto() {
        System.out.println("\n=== Test 18: Messaggio completo con tutti i campi ===");

        messaggio.setAutore(autore);
        messaggio.setDestinatario(destinatario);
        messaggio.setBody("Messaggio di prova completo");
        messaggio.setDateTime(LocalDateTime.of(2024, 6, 15, 14, 30));
        messaggio.setTopic(topic);

        assertNotNull(messaggio.getAutore());
        assertNotNull(messaggio.getDestinatario());
        assertNotNull(messaggio.getBody());
        assertNotNull(messaggio.getDateTime());
        assertNotNull(messaggio.getTopic());

        assertEquals("studente@studenti.unisa.it", messaggio.getAutore().getEmail());
        assertEquals("docente@unisa.it", messaggio.getDestinatario().getEmail());
        assertEquals("Messaggio di prova completo", messaggio.getBody());
        assertEquals(2024, messaggio.getDateTime().getYear());
        assertEquals("Esame", messaggio.getTopic().getNome());

        System.out.println("✓ Messaggio completo validato con successo");
    }

    @Test
    public void testModificaCampiMessaggio() {
        System.out.println("\n=== Test 19: Modifica campi esistenti ===");

        // Imposta valori iniziali
        messaggio.setAutore(autore);
        messaggio.setBody("Primo messaggio");
        messaggio.setDateTime(LocalDateTime.now().minusDays(1));

        assertEquals("Primo messaggio", messaggio.getBody());

        // Modifica i valori
        messaggio.setAutore(destinatario);
        messaggio.setBody("Messaggio modificato");
        messaggio.setDateTime(LocalDateTime.now());

        assertEquals(destinatario, messaggio.getAutore());
        assertEquals("Messaggio modificato", messaggio.getBody());

        System.out.println("✓ Modifica campi funziona correttamente");
    }

    @Test
    public void testMessaggioDiversiAutoriDestinatari() {
        System.out.println("\n=== Test 20: Messaggi con autori/destinatari diversi ===");

        Messaggio msg1 = new Messaggio();
        msg1.setAutore(autore);
        msg1.setDestinatario(destinatario);

        Messaggio msg2 = new Messaggio();
        msg2.setAutore(destinatario);
        msg2.setDestinatario(autore);

        assertNotEquals(msg1.getAutore(), msg2.getAutore());
        assertNotEquals(msg1.getDestinatario(), msg2.getDestinatario());
        assertEquals(msg1.getAutore(), msg2.getDestinatario());
        assertEquals(msg1.getDestinatario(), msg2.getAutore());

        System.out.println("✓ Messaggi con autori/destinatari scambiati gestiti correttamente");
    }

    @Test
    public void testCostantiNamedQueries() {
        System.out.println("\n=== Test 21: Verifica costanti NamedQueries ===");

        assertEquals("Messaggio.trovaMessaggio", Messaggio.TROVA_MESSAGGIO);
        assertEquals("Messaggio.trovaMessaggiInviati", Messaggio.TROVA_MESSAGGI_INVIATI);
        assertEquals("Messaggio.trovaMessaggiRicevuti", Messaggio.TROVA_MESSAGGI_RICEVUTI);
        assertEquals("Messaggio.trovaMessaggiMessaggeri", Messaggio.TROVA_MESSAGGI_MESSAGGERI);
        assertEquals("Messaggio.trovaTutti", Messaggio.TROVA_TUTTI);
        assertEquals("Messaggio.trovaAvvisi", Messaggio.TROVA_AVVISI);
        assertEquals("Messaggio.trovaAvvisiAutore", Messaggio.TROVA_AVVISI_AUTORE);
        assertEquals("Messaggio.trovaMessaggiData", Messaggio.TROVA_MESSAGGI_DATA);
        assertEquals("Messaggio.trovaTopic", Messaggio.TROVA_TOPIC);

        System.out.println("✓ Tutte le 9 costanti NamedQueries verificate");
    }

    @Test
    public void testMessaggioConTopicComplesso() {
        System.out.println("\n=== Test 22: Messaggio con Topic complesso ===");

        Topic topicComplesso = new Topic();
        topicComplesso.setNome("Programmazione Distribuita - Lezione 5");
        topicComplesso.setCorsoLaurea(corsoLaurea);

        messaggio.setTopic(topicComplesso);
        messaggio.setBody("Contenuto relativo alla lezione");
        messaggio.setAutore(destinatario); // Docente come autore

        assertEquals(topicComplesso, messaggio.getTopic());
        assertEquals("Programmazione Distribuita - Lezione 5", messaggio.getTopic().getNome());
        assertInstanceOf(Docente.class, messaggio.getAutore());

        System.out.println("✓ Topic complesso gestito correttamente");
    }

    @Test
    public void testCostruttoreCompletoConTuttiIParametri() {
        System.out.println("\n=== Test 23: Costruttore completo - verifica tutti i parametri ===");

        LocalDateTime specificTime = LocalDateTime.of(2024, 11, 30, 10, 15, 30);
        String specificBody = "Messaggio specifico per test costruttore";

        Messaggio msg = new Messaggio(autore, destinatario, topic, specificBody, specificTime);

        // Verifica ogni campo individualmente
        assertSame(autore, msg.getAutore());
        assertSame(destinatario, msg.getDestinatario());
        assertSame(topic, msg.getTopic());
        assertEquals(specificBody, msg.getBody());
        assertEquals(specificTime, msg.getDateTime());
        assertEquals(2024, msg.getDateTime().getYear());
        assertEquals(11, msg.getDateTime().getMonthValue());
        assertEquals(30, msg.getDateTime().getDayOfMonth());

        System.out.println("✓ Costruttore completo: tutti i parametri verificati individualmente");
    }

    @Test
    public void testMultipleSettersInSequence() {
        System.out.println("\n=== Test 24: Multiple setters in sequenza ===");

        Messaggio msg = new Messaggio();

        // Chain di setters
        msg.setAutore(autore);
        msg.setDestinatario(destinatario);
        msg.setBody("Test");
        msg.setDateTime(LocalDateTime.now());
        msg.setTopic(topic);

        // Verifica che tutti i valori siano stati impostati
        assertNotNull(msg.getAutore());
        assertNotNull(msg.getDestinatario());
        assertNotNull(msg.getBody());
        assertNotNull(msg.getDateTime());
        assertNotNull(msg.getTopic());

        // Sovrascrivi i valori
        Accademico nuovoAutore = new Studente();
        nuovoAutore.setEmail("nuovo@studenti.unisa.it");
        msg.setAutore(nuovoAutore);
        msg.setBody("Nuovo body");

        assertEquals(nuovoAutore, msg.getAutore());
        assertEquals("Nuovo body", msg.getBody());

        System.out.println("✓ Multiple setters e sovrascritture gestiti correttamente");
    }

    @Test
    public void testBodyConNewlines() {
        System.out.println("\n=== Test 25: Body con newlines e caratteri speciali ===");

        String bodyMultiline = "Riga 1\nRiga 2\nRiga 3\tcon tab\r\nRiga 4";
        messaggio.setBody(bodyMultiline);

        assertEquals(bodyMultiline, messaggio.getBody());
        assertTrue(messaggio.getBody().contains("\n"));
        assertTrue(messaggio.getBody().contains("\t"));

        System.out.println("✓ Body multilinea gestito correttamente");
    }
}
