package it.unisa.uniclass.testing.unit.conversazioni.service.dao;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioDAO;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import jakarta.persistence.EntityManager;
import jakarta.persistence.TypedQuery;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.lang.reflect.Field;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test completi per la classe MessaggioDAO.
 * Coverage massimizzata per JaCoCo: tutti i metodi del DAO.
 */
public class MessaggioDAOTest {

    @Mock
    private EntityManager entityManager;

    @Mock
    private TypedQuery<Messaggio> typedQuery;

    @InjectMocks
    private MessaggioDAO messaggioDAO;

    private Messaggio messaggio;
    private Accademico autore;
    private Accademico destinatario;
    private Topic topic;
    private LocalDateTime dateTime;

    @BeforeEach
    public void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);

        // Inject EntityManager usando reflection
        messaggioDAO = new MessaggioDAO();
        Field emField = MessaggioDAO.class.getDeclaredField("emUniClass");
        emField.setAccessible(true);
        emField.set(messaggioDAO, entityManager);

        // Setup CorsoLaurea
        CorsoLaurea corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");

        // Setup Autore
        autore = new Studente();
        autore.setEmail("autore@studenti.unisa.it");
        autore.setNome("Mario");
        autore.setCognome("Rossi");
        autore.setMatricola("0512100001");

        // Setup Destinatario
        destinatario = new Studente();
        destinatario.setEmail("destinatario@studenti.unisa.it");
        destinatario.setNome("Luigi");
        destinatario.setCognome("Verdi");
        destinatario.setMatricola("0512100002");

        // Setup Topic
        topic = new Topic();
        topic.setNome("Esame");
        topic.setCorsoLaurea(corsoLaurea);

        // Setup DateTime
        dateTime = LocalDateTime.of(2024, 11, 30, 10, 0);

        // Setup Messaggio
        messaggio = new Messaggio();
        messaggio.setAutore(autore);
        messaggio.setDestinatario(destinatario);
        messaggio.setBody("Messaggio di test");
        messaggio.setDateTime(dateTime);
        messaggio.setTopic(topic);
    }

    @Test
    public void testTrovaMessaggio() {
        System.out.println("\n=== Test 1: trovaMessaggio ===");

        long id = 1L;

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGIO), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("id"), eq(id))).thenReturn(typedQuery);
        when(typedQuery.getSingleResult()).thenReturn(messaggio);

        Messaggio result = messaggioDAO.trovaMessaggio(id);

        assertNotNull(result);
        assertEquals(messaggio, result);
        verify(entityManager).createNamedQuery(Messaggio.TROVA_MESSAGGIO, Messaggio.class);
        verify(typedQuery).setParameter("id", id);
        verify(typedQuery).getSingleResult();

        System.out.println("✓ trovaMessaggio funziona correttamente");
    }

    @Test
    public void testTrovaMessaggiInviati() {
        System.out.println("\n=== Test 2: trovaMessaggiInviati ===");

        String matricola = "0512100001";
        List<Messaggio> messaggi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_INVIATI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("matricola"), eq(matricola))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaMessaggiInviati(matricola);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(messaggio, result.getFirst());
        verify(entityManager).createNamedQuery(Messaggio.TROVA_MESSAGGI_INVIATI, Messaggio.class);
        verify(typedQuery).setParameter("matricola", matricola);
        verify(typedQuery).getResultList();

        System.out.println("✓ trovaMessaggiInviati restituisce " + result.size() + " messaggi");
    }

    @Test
    public void testTrovaMessaggiInviatiListaVuota() {
        System.out.println("\n=== Test 3: trovaMessaggiInviati - lista vuota ===");

        String matricola = "9999999999";

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_INVIATI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("matricola"), eq(matricola))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(new ArrayList<>());

        List<Messaggio> result = messaggioDAO.trovaMessaggiInviati(matricola);

        assertNotNull(result);
        assertTrue(result.isEmpty());

        System.out.println("✓ Lista vuota gestita correttamente");
    }

    @Test
    public void testTrovaMessaggiRicevuti() {
        System.out.println("\n=== Test 4: trovaMessaggiRicevuti ===");

        String matricola = "0512100002";
        List<Messaggio> messaggi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_RICEVUTI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("matricola"), eq(matricola))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaMessaggiRicevuti(matricola);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(messaggio, result.getFirst());
        verify(entityManager).createNamedQuery(Messaggio.TROVA_MESSAGGI_RICEVUTI, Messaggio.class);
        verify(typedQuery).setParameter("matricola", matricola);

        System.out.println("✓ trovaMessaggiRicevuti funziona correttamente");
    }

    @Test
    public void testTrovaMessaggiRicevutiMultipli() {
        System.out.println("\n=== Test 5: trovaMessaggiRicevuti - multipli ===");

        String matricola = "0512100002";

        Messaggio msg1 = new Messaggio();
        msg1.setBody("Messaggio 1");
        Messaggio msg2 = new Messaggio();
        msg2.setBody("Messaggio 2");
        Messaggio msg3 = new Messaggio();
        msg3.setBody("Messaggio 3");

        List<Messaggio> messaggi = Arrays.asList(msg1, msg2, msg3);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_RICEVUTI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("matricola"), eq(matricola))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaMessaggiRicevuti(matricola);

        assertEquals(3, result.size());

        System.out.println("✓ " + result.size() + " messaggi ricevuti");
    }

    @Test
    public void testTrovaMessaggi() {
        System.out.println("\n=== Test 6: trovaMessaggi (tra due utenti) ===");

        String matricola1 = "0512100001";
        String matricola2 = "0512100002";
        List<Messaggio> messaggi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_MESSAGGERI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("autore"), eq(matricola1))).thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("destinatario"), eq(matricola2))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaMessaggi(matricola1, matricola2);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(typedQuery).setParameter("autore", matricola1);
        verify(typedQuery).setParameter("destinatario", matricola2);

        System.out.println("✓ trovaMessaggi tra due utenti funziona");
    }

    @Test
    public void testTrovaTutti() {
        System.out.println("\n=== Test 7: trovaTutti ===");

        Messaggio msg1 = new Messaggio();
        Messaggio msg2 = new Messaggio();
        List<Messaggio> messaggi = Arrays.asList(msg1, msg2, messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_TUTTI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaTutti();

        assertNotNull(result);
        assertEquals(3, result.size());
        verify(entityManager).createNamedQuery(Messaggio.TROVA_TUTTI, Messaggio.class);
        verify(typedQuery).getResultList();

        System.out.println("✓ trovaTutti restituisce " + result.size() + " messaggi");
    }

    @Test
    public void testTrovaTuttiListaVuota() {
        System.out.println("\n=== Test 8: trovaTutti - lista vuota ===");

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_TUTTI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(new ArrayList<>());

        List<Messaggio> result = messaggioDAO.trovaTutti();

        assertNotNull(result);
        assertTrue(result.isEmpty());

        System.out.println("✓ Lista vuota gestita correttamente");
    }

    @Test
    public void testTrovaAvvisi() {
        System.out.println("\n=== Test 9: trovaAvvisi ===");

        List<Messaggio> avvisi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_AVVISI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(avvisi);

        List<Messaggio> result = messaggioDAO.trovaAvvisi();

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(entityManager).createNamedQuery(Messaggio.TROVA_AVVISI, Messaggio.class);

        System.out.println("✓ trovaAvvisi funziona correttamente");
    }

    @Test
    public void testTrovaAvvisiMultipli() {
        System.out.println("\n=== Test 10: trovaAvvisi - multipli ===");

        Messaggio avviso1 = new Messaggio();
        avviso1.setTopic(topic);
        Messaggio avviso2 = new Messaggio();
        avviso2.setTopic(topic);

        List<Messaggio> avvisi = Arrays.asList(avviso1, avviso2, messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_AVVISI), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(avvisi);

        List<Messaggio> result = messaggioDAO.trovaAvvisi();

        assertEquals(3, result.size());

        System.out.println("✓ " + result.size() + " avvisi trovati");
    }

    @Test
    public void testTrovaAvvisiAutore() {
        System.out.println("\n=== Test 11: trovaAvvisiAutore ===");

        String autoreMatricola = "0512100001";
        List<Messaggio> avvisi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_AVVISI_AUTORE), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("autore"), eq(autoreMatricola))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(avvisi);

        List<Messaggio> result = messaggioDAO.trovaAvvisiAutore(autoreMatricola);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(typedQuery).setParameter("autore", autoreMatricola);

        System.out.println("✓ trovaAvvisiAutore funziona correttamente");
    }

    @Test
    public void testTrovaMessaggiData() {
        System.out.println("\n=== Test 12: trovaMessaggiData ===");

        List<Messaggio> messaggi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_DATA), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("dateTime"), eq(dateTime))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaMessaggiData(dateTime);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(typedQuery).setParameter("dateTime", dateTime);

        System.out.println("✓ trovaMessaggiData funziona per " + dateTime);
    }

    @Test
    public void testTrovaMessaggiDataDiverseDate() {
        System.out.println("\n=== Test 13: trovaMessaggiData - diverse date ===");

        LocalDateTime data1 = LocalDateTime.of(2024, 1, 1, 10, 0);
        LocalDateTime data2 = LocalDateTime.of(2024, 12, 31, 23, 59);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_MESSAGGI_DATA), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(anyString(), any(LocalDateTime.class))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(new ArrayList<>());

        List<Messaggio> result1 = messaggioDAO.trovaMessaggiData(data1);
        List<Messaggio> result2 = messaggioDAO.trovaMessaggiData(data2);

        assertNotNull(result1);
        assertNotNull(result2);

        System.out.println("✓ Diverse date gestite correttamente");
    }

    @Test
    public void testTrovaTopic() {
        System.out.println("\n=== Test 14: trovaTopic ===");

        List<Messaggio> messaggi = List.of(messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_TOPIC), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("topic"), eq(topic))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaTopic(topic);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(typedQuery).setParameter("topic", topic);

        System.out.println("✓ trovaTopic funziona correttamente");
    }

    @Test
    public void testTrovaTopicMultipli() {
        System.out.println("\n=== Test 15: trovaTopic - multipli messaggi ===");

        Messaggio msg1 = new Messaggio();
        msg1.setTopic(topic);
        Messaggio msg2 = new Messaggio();
        msg2.setTopic(topic);

        List<Messaggio> messaggi = Arrays.asList(msg1, msg2, messaggio);

        when(entityManager.createNamedQuery(eq(Messaggio.TROVA_TOPIC), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(eq("topic"), eq(topic))).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(messaggi);

        List<Messaggio> result = messaggioDAO.trovaTopic(topic);

        assertEquals(3, result.size());

        System.out.println("✓ " + result.size() + " messaggi con stesso topic");
    }

    @Test
    public void testAggiungiMessaggioNuovo() {
        System.out.println("\n=== Test 16: aggiungiMessaggio - nuovo (ID null) ===");

        Messaggio nuovoMessaggio = new Messaggio();
        nuovoMessaggio.setBody("Nuovo messaggio");
        // ID è null per nuovo messaggio

        doNothing().when(entityManager).persist(any(Messaggio.class));
        doNothing().when(entityManager).flush();

        Messaggio result = messaggioDAO.aggiungiMessaggio(nuovoMessaggio);

        assertNotNull(result);
        verify(entityManager).persist(nuovoMessaggio);
        verify(entityManager).flush();
        verify(entityManager, never()).merge(any(Messaggio.class));

        System.out.println("✓ Nuovo messaggio aggiunto con persist()");
    }

    @Test
    public void testAggiungiMessaggioEsistente() throws Exception {
        System.out.println("\n=== Test 17: aggiungiMessaggio - esistente (ID non null) ===");

        // Set ID usando reflection per simulare messaggio esistente
        Messaggio messaggioEsistente = new Messaggio();
        messaggioEsistente.setBody("Messaggio esistente");

        Field idField = Messaggio.class.getDeclaredField("id");
        idField.setAccessible(true);
        idField.set(messaggioEsistente, 100L);

        when(entityManager.merge(any(Messaggio.class))).thenReturn(messaggioEsistente);
        doNothing().when(entityManager).flush();

        Messaggio result = messaggioDAO.aggiungiMessaggio(messaggioEsistente);

        assertNotNull(result);
        verify(entityManager).merge(messaggioEsistente);
        verify(entityManager).flush();
        verify(entityManager, never()).persist(any(Messaggio.class));

        System.out.println("✓ Messaggio esistente aggiornato con merge()");
    }

    @Test
    public void testAggiungiMessaggioConFlush() {
        System.out.println("\n=== Test 18: aggiungiMessaggio - verifica flush ===");

        Messaggio msg = new Messaggio();
        msg.setBody("Test flush");

        doNothing().when(entityManager).persist(any(Messaggio.class));
        doNothing().when(entityManager).flush();

        messaggioDAO.aggiungiMessaggio(msg);

        verify(entityManager).flush();

        System.out.println("✓ Flush chiamato correttamente");
    }

    @Test
    public void testRimuoviMessaggio() {
        System.out.println("\n=== Test 19: rimuoviMessaggio ===");

        doNothing().when(entityManager).remove(any(Messaggio.class));

        messaggioDAO.rimuoviMessaggio(messaggio);

        verify(entityManager).remove(messaggio);

        System.out.println("✓ rimuoviMessaggio funziona correttamente");
    }

    @Test
    public void testRimuoviMessaggioMultipli() {
        System.out.println("\n=== Test 20: rimuoviMessaggio - multipli ===");

        Messaggio msg1 = new Messaggio();
        Messaggio msg2 = new Messaggio();
        Messaggio msg3 = new Messaggio();

        doNothing().when(entityManager).remove(any(Messaggio.class));

        messaggioDAO.rimuoviMessaggio(msg1);
        messaggioDAO.rimuoviMessaggio(msg2);
        messaggioDAO.rimuoviMessaggio(msg3);

        verify(entityManager, times(3)).remove(any(Messaggio.class));

        System.out.println("✓ 3 messaggi rimossi correttamente");
    }

    @Test
    public void testTuttiIMetodiQuery() {
        System.out.println("\n=== Test 21: Verifica tutte le NamedQueries ===");

        when(entityManager.createNamedQuery(anyString(), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.setParameter(anyString(), any())).thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(new ArrayList<>());
        when(typedQuery.getSingleResult()).thenReturn(messaggio);

        // Testa tutte le query
        messaggioDAO.trovaMessaggio(1L);
        messaggioDAO.trovaMessaggiInviati("123");
        messaggioDAO.trovaMessaggiRicevuti("123");
        messaggioDAO.trovaMessaggi("123", "456");
        messaggioDAO.trovaTutti();
        messaggioDAO.trovaAvvisi();
        messaggioDAO.trovaAvvisiAutore("123");
        messaggioDAO.trovaMessaggiData(LocalDateTime.now());
        messaggioDAO.trovaTopic(topic);

        // Verifica che tutte le query siano state chiamate
        verify(entityManager, times(9)).createNamedQuery(anyString(), eq(Messaggio.class));

        System.out.println("✓ Tutte le 9 query verificate");
    }

    @Test
    public void testSequenzaCompleta() {
        System.out.println("\n=== Test 22: Sequenza completa - aggiungi, trova, rimuovi ===");

        Messaggio msg = new Messaggio();
        msg.setBody("Test sequenza");

        // Aggiungi
        doNothing().when(entityManager).persist(any(Messaggio.class));
        doNothing().when(entityManager).flush();
        messaggioDAO.aggiungiMessaggio(msg);
        verify(entityManager).persist(msg);

        // Trova
        when(entityManager.createNamedQuery(anyString(), eq(Messaggio.class)))
                .thenReturn(typedQuery);
        when(typedQuery.getResultList()).thenReturn(List.of(msg));
        List<Messaggio> trovati = messaggioDAO.trovaTutti();
        assertEquals(1, trovati.size());

        // Rimuovi
        doNothing().when(entityManager).remove(any(Messaggio.class));
        messaggioDAO.rimuoviMessaggio(msg);
        verify(entityManager).remove(msg);

        System.out.println("✓ Sequenza completa eseguita con successo");
    }
}
