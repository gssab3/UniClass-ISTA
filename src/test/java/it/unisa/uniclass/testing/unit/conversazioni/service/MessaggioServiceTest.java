package it.unisa.uniclass.testing.unit.conversazioni.service;

import it.unisa.uniclass.conversazioni.model.Messaggio;
import it.unisa.uniclass.conversazioni.model.Topic;
import it.unisa.uniclass.conversazioni.service.MessaggioService;
import it.unisa.uniclass.conversazioni.service.dao.MessaggioRemote;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.MockitoAnnotations;

import javax.naming.InitialContext;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Test completi per la classe MessaggioService.
 * Coverage massimizzata per JaCoCo: tutti i metodi del service.
 */
public class MessaggioServiceTest {

    @Mock
    private MessaggioRemote messaggioDao;

    private MessaggioService messaggioService;

    private Messaggio messaggio;
    private Accademico autore;
    private Accademico destinatario;
    private Topic topic;
    private LocalDateTime dateTime;

    @BeforeEach
    public void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);

        // Mock InitialContext per evitare JNDI lookup nel costruttore
        try (@SuppressWarnings("unused") MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                (mock, context) -> when(mock.lookup(anyString())).thenReturn(messaggioDao))) {
            messaggioService = new MessaggioService();
        }

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
        when(messaggioDao.trovaMessaggio(id)).thenReturn(messaggio);

        Messaggio result = messaggioService.trovaMessaggio(id);

        assertNotNull(result);
        assertEquals(messaggio, result);
        assertEquals("Messaggio di test", result.getBody());
        verify(messaggioDao).trovaMessaggio(id);

        System.out.println("✓ trovaMessaggio funziona correttamente");
    }

    @Test
    public void testTrovaMessaggioNoResultException() {
        System.out.println("\n=== Test 2: trovaMessaggio - NoResultException ===");

        long id = 999L;
        when(messaggioDao.trovaMessaggio(id)).thenThrow(new NoResultException());

        Messaggio result = messaggioService.trovaMessaggio(id);

        assertNull(result);
        verify(messaggioDao).trovaMessaggio(id);

        System.out.println("✓ NoResultException gestita correttamente, ritorna null");
    }

    @Test
    public void testTrovaMessaggiInviati() {
        System.out.println("\n=== Test 3: trovaMessaggiInviati ===");

        String matricola = "0512100001";
        List<Messaggio> messaggi = List.of(messaggio);

        when(messaggioDao.trovaMessaggiInviati(matricola)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaMessaggiInviati(matricola);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(messaggio, result.getFirst());
        verify(messaggioDao).trovaMessaggiInviati(matricola);

        System.out.println("✓ trovaMessaggiInviati restituisce " + result.size() + " messaggi");
    }

    @Test
    public void testTrovaMessaggiInviatiVuoto() {
        System.out.println("\n=== Test 4: trovaMessaggiInviati - lista vuota ===");

        String matricola = "9999999999";
        when(messaggioDao.trovaMessaggiInviati(matricola)).thenReturn(new ArrayList<>());

        List<Messaggio> result = messaggioService.trovaMessaggiInviati(matricola);

        assertNotNull(result);
        assertTrue(result.isEmpty());

        System.out.println("✓ Lista vuota gestita correttamente");
    }

    @Test
    public void testTrovaMessaggiRicevuti() {
        System.out.println("\n=== Test 5: trovaMessaggiRicevuti ===");

        String matricola = "0512100002";
        List<Messaggio> messaggi = List.of(messaggio);

        when(messaggioDao.trovaMessaggiRicevuti(matricola)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaMessaggiRicevuti(matricola);

        assertNotNull(result);
        assertEquals(1, result.size());
        assertEquals(messaggio, result.getFirst());
        verify(messaggioDao).trovaMessaggiRicevuti(matricola);

        System.out.println("✓ trovaMessaggiRicevuti funziona correttamente");
    }

    @Test
    public void testTrovaMessaggiRicevutiMultipli() {
        System.out.println("\n=== Test 6: trovaMessaggiRicevuti - multipli ===");

        String matricola = "0512100002";
        Messaggio msg1 = new Messaggio();
        msg1.setBody("Messaggio 1");
        Messaggio msg2 = new Messaggio();
        msg2.setBody("Messaggio 2");
        Messaggio msg3 = new Messaggio();
        msg3.setBody("Messaggio 3");

        List<Messaggio> messaggi = Arrays.asList(msg1, msg2, msg3);
        when(messaggioDao.trovaMessaggiRicevuti(matricola)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaMessaggiRicevuti(matricola);

        assertEquals(3, result.size());

        System.out.println("✓ " + result.size() + " messaggi ricevuti");
    }

    @Test
    public void testTrovaMessaggi() {
        System.out.println("\n=== Test 7: trovaMessaggi tra due utenti ===");

        String matricola1 = "0512100001";
        String matricola2 = "0512100002";
        List<Messaggio> messaggi = List.of(messaggio);

        when(messaggioDao.trovaMessaggi(matricola1, matricola2)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaMessaggi(matricola1, matricola2);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(messaggioDao).trovaMessaggi(matricola1, matricola2);

        System.out.println("✓ trovaMessaggi tra due utenti funziona");
    }

    @Test
    public void testTrovaTutti() {
        System.out.println("\n=== Test 8: trovaTutti ===");

        Messaggio msg1 = new Messaggio();
        Messaggio msg2 = new Messaggio();
        List<Messaggio> messaggi = Arrays.asList(msg1, msg2, messaggio);

        when(messaggioDao.trovaTutti()).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaTutti();

        assertNotNull(result);
        assertEquals(3, result.size());
        verify(messaggioDao).trovaTutti();

        System.out.println("✓ trovaTutti restituisce " + result.size() + " messaggi");
    }

    @Test
    public void testTrovaAvvisi() {
        System.out.println("\n=== Test 9: trovaAvvisi ===");

        List<Messaggio> avvisi = List.of(messaggio);
        when(messaggioDao.trovaAvvisi()).thenReturn(avvisi);

        List<Messaggio> result = messaggioService.trovaAvvisi();

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(messaggioDao).trovaAvvisi();

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
        when(messaggioDao.trovaAvvisi()).thenReturn(avvisi);

        List<Messaggio> result = messaggioService.trovaAvvisi();

        assertEquals(3, result.size());

        System.out.println("✓ " + result.size() + " avvisi trovati");
    }

    @Test
    public void testTrovaAvvisiAutore() {
        System.out.println("\n=== Test 11: trovaAvvisiAutore ===");

        String autoreMatricola = "0512100001";
        List<Messaggio> avvisi = List.of(messaggio);

        when(messaggioDao.trovaAvvisiAutore(autoreMatricola)).thenReturn(avvisi);

        List<Messaggio> result = messaggioService.trovaAvvisiAutore(autoreMatricola);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(messaggioDao).trovaAvvisiAutore(autoreMatricola);

        System.out.println("✓ trovaAvvisiAutore funziona correttamente");
    }

    @Test
    public void testTrovaMessaggiData() {
        System.out.println("\n=== Test 12: trovaMessaggiData ===");

        List<Messaggio> messaggi = List.of(messaggio);
        when(messaggioDao.trovaMessaggiData(dateTime)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaMessaggiData(dateTime);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(messaggioDao).trovaMessaggiData(dateTime);

        System.out.println("✓ trovaMessaggiData funziona per " + dateTime);
    }

    @Test
    public void testTrovaMessaggiDataDiverseDate() {
        System.out.println("\n=== Test 13: trovaMessaggiData - diverse date ===");

        LocalDateTime data1 = LocalDateTime.of(2024, 1, 1, 10, 0);
        LocalDateTime data2 = LocalDateTime.of(2024, 12, 31, 23, 59);

        when(messaggioDao.trovaMessaggiData(any(LocalDateTime.class))).thenReturn(new ArrayList<>());

        List<Messaggio> result1 = messaggioService.trovaMessaggiData(data1);
        List<Messaggio> result2 = messaggioService.trovaMessaggiData(data2);

        assertNotNull(result1);
        assertNotNull(result2);
        verify(messaggioDao, times(2)).trovaMessaggiData(any(LocalDateTime.class));

        System.out.println("✓ Diverse date gestite correttamente");
    }

    @Test
    public void testTrovaMessaggeriDiUnAccademico() {
        System.out.println("\n=== Test 14: trovaMessaggeriDiUnAccademico ===");

        String matricola = "0512100002";

        // Setup messaggi ricevuti con destinatari diversi
        Messaggio msg1 = new Messaggio();
        msg1.setDestinatario(destinatario);
        Messaggio msg2 = new Messaggio();
        Accademico dest2 = new Studente();
        dest2.setEmail("altro@studenti.unisa.it");
        msg2.setDestinatario(dest2);

        List<Messaggio> messaggiRicevuti = Arrays.asList(msg1, msg2);
        when(messaggioDao.trovaMessaggiRicevuti(matricola)).thenReturn(messaggiRicevuti);

        List<Accademico> result = messaggioService.trovaMessaggeriDiUnAccademico(matricola);

        assertNotNull(result);
        assertEquals(2, result.size());
        assertTrue(result.contains(destinatario));
        assertTrue(result.contains(dest2));
        verify(messaggioDao).trovaMessaggiRicevuti(matricola);

        System.out.println("✓ trovaMessaggeriDiUnAccademico restituisce " + result.size() + " accademici");
    }

    @Test
    public void testTrovaMessaggeriDiUnAccademicoVuoto() {
        System.out.println("\n=== Test 15: trovaMessaggeriDiUnAccademico - nessun messaggio ===");

        String matricola = "9999999999";
        when(messaggioDao.trovaMessaggiRicevuti(matricola)).thenReturn(new ArrayList<>());

        List<Accademico> result = messaggioService.trovaMessaggeriDiUnAccademico(matricola);

        assertNotNull(result);
        assertTrue(result.isEmpty());

        System.out.println("✓ Lista vuota di accademici gestita correttamente");
    }

    @Test
    public void testTrovaTopic() {
        System.out.println("\n=== Test 16: trovaTopic ===");

        List<Messaggio> messaggi = List.of(messaggio);
        when(messaggioDao.trovaTopic(topic)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaTopic(topic);

        assertNotNull(result);
        assertEquals(1, result.size());
        verify(messaggioDao).trovaTopic(topic);

        System.out.println("✓ trovaTopic funziona correttamente");
    }

    @Test
    public void testTrovaTopicMultipli() {
        System.out.println("\n=== Test 17: trovaTopic - multipli messaggi ===");

        Messaggio msg1 = new Messaggio();
        msg1.setTopic(topic);
        Messaggio msg2 = new Messaggio();
        msg2.setTopic(topic);

        List<Messaggio> messaggi = Arrays.asList(msg1, msg2, messaggio);
        when(messaggioDao.trovaTopic(topic)).thenReturn(messaggi);

        List<Messaggio> result = messaggioService.trovaTopic(topic);

        assertEquals(3, result.size());

        System.out.println("✓ " + result.size() + " messaggi con stesso topic");
    }

    @Test
    public void testAggiungiMessaggio() {
        System.out.println("\n=== Test 18: aggiungiMessaggio ===");

        when(messaggioDao.aggiungiMessaggio(messaggio)).thenReturn(messaggio);

        Messaggio result = messaggioService.aggiungiMessaggio(messaggio);

        assertNotNull(result);
        assertEquals(messaggio, result);
        verify(messaggioDao).aggiungiMessaggio(messaggio);

        System.out.println("✓ aggiungiMessaggio funziona correttamente");
    }

    @Test
    public void testAggiungiMessaggioNull() {
        System.out.println("\n=== Test 19: aggiungiMessaggio - messaggio null ===");

        Messaggio result = messaggioService.aggiungiMessaggio(null);

        assertNull(result);
        verify(messaggioDao, never()).aggiungiMessaggio(any());

        System.out.println("✓ Messaggio null gestito correttamente (non chiamato DAO)");
    }

    @Test
    public void testAggiungiMessaggioNuovo() {
        System.out.println("\n=== Test 20: aggiungiMessaggio - nuovo messaggio ===");

        Messaggio nuovoMsg = new Messaggio();
        nuovoMsg.setBody("Nuovo messaggio");
        nuovoMsg.setAutore(autore);
        nuovoMsg.setDestinatario(destinatario);

        when(messaggioDao.aggiungiMessaggio(nuovoMsg)).thenReturn(nuovoMsg);

        Messaggio result = messaggioService.aggiungiMessaggio(nuovoMsg);

        assertNotNull(result);
        assertEquals("Nuovo messaggio", result.getBody());
        verify(messaggioDao).aggiungiMessaggio(nuovoMsg);

        System.out.println("✓ Nuovo messaggio aggiunto");
    }

    @Test
    public void testRimuoviMessaggio() {
        System.out.println("\n=== Test 21: rimuoviMessaggio ===");

        doNothing().when(messaggioDao).rimuoviMessaggio(messaggio);

        messaggioService.rimuoviMessaggio(messaggio);

        verify(messaggioDao).rimuoviMessaggio(messaggio);

        System.out.println("✓ rimuoviMessaggio funziona correttamente");
    }

    @Test
    public void testRimuoviMessaggioNull() {
        System.out.println("\n=== Test 22: rimuoviMessaggio - messaggio null ===");

        messaggioService.rimuoviMessaggio(null);

        verify(messaggioDao, never()).rimuoviMessaggio(any());

        System.out.println("✓ Messaggio null gestito correttamente (non chiamato DAO)");
    }

    @Test
    public void testRimuoviMessaggioMultipli() {
        System.out.println("\n=== Test 23: rimuoviMessaggio - multipli ===");

        Messaggio msg1 = new Messaggio();
        Messaggio msg2 = new Messaggio();
        Messaggio msg3 = new Messaggio();

        doNothing().when(messaggioDao).rimuoviMessaggio(any(Messaggio.class));

        messaggioService.rimuoviMessaggio(msg1);
        messaggioService.rimuoviMessaggio(msg2);
        messaggioService.rimuoviMessaggio(msg3);

        verify(messaggioDao, times(3)).rimuoviMessaggio(any(Messaggio.class));

        System.out.println("✓ 3 messaggi rimossi correttamente");
    }

    @Test
    public void testTuttiIMetodi() {
        System.out.println("\n=== Test 24: Verifica tutti i metodi del service ===");

        // Setup mocks
        when(messaggioDao.trovaMessaggio(anyLong())).thenReturn(messaggio);
        when(messaggioDao.trovaMessaggiInviati(anyString())).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaMessaggiRicevuti(anyString())).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaMessaggi(anyString(), anyString())).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaTutti()).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaAvvisi()).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaAvvisiAutore(anyString())).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaMessaggiData(any(LocalDateTime.class))).thenReturn(new ArrayList<>());
        when(messaggioDao.trovaTopic(any(Topic.class))).thenReturn(new ArrayList<>());
        when(messaggioDao.aggiungiMessaggio(any(Messaggio.class))).thenReturn(messaggio);
        doNothing().when(messaggioDao).rimuoviMessaggio(any(Messaggio.class));

        // Chiama tutti i metodi
        messaggioService.trovaMessaggio(1L);
        messaggioService.trovaMessaggiInviati("123");
        messaggioService.trovaMessaggiRicevuti("123");
        messaggioService.trovaMessaggi("123", "456");
        messaggioService.trovaTutti();
        messaggioService.trovaAvvisi();
        messaggioService.trovaAvvisiAutore("123");
        messaggioService.trovaMessaggiData(LocalDateTime.now());
        messaggioService.trovaMessaggeriDiUnAccademico("123");
        messaggioService.trovaTopic(topic);
        messaggioService.aggiungiMessaggio(messaggio);
        messaggioService.rimuoviMessaggio(messaggio);

        // Verifica chiamate
        verify(messaggioDao).trovaMessaggio(anyLong());
        verify(messaggioDao, times(2)).trovaMessaggiRicevuti(anyString()); // chiamato 2 volte
        verify(messaggioDao).trovaMessaggiInviati(anyString());
        verify(messaggioDao).trovaMessaggi(anyString(), anyString());
        verify(messaggioDao).trovaTutti();
        verify(messaggioDao).trovaAvvisi();
        verify(messaggioDao).trovaAvvisiAutore(anyString());
        verify(messaggioDao).trovaMessaggiData(any(LocalDateTime.class));
        verify(messaggioDao).trovaTopic(any(Topic.class));
        verify(messaggioDao).aggiungiMessaggio(any(Messaggio.class));
        verify(messaggioDao).rimuoviMessaggio(any(Messaggio.class));

        System.out.println("✓ Tutti i 12 metodi pubblici verificati");
    }

    @Test
    public void testSequenzaCompleta() {
        System.out.println("\n=== Test 25: Sequenza completa - aggiungi, trova, rimuovi ===");

        Messaggio msg = new Messaggio();
        msg.setBody("Test sequenza");

        // Aggiungi
        when(messaggioDao.aggiungiMessaggio(msg)).thenReturn(msg);
        Messaggio aggiunto = messaggioService.aggiungiMessaggio(msg);
        assertNotNull(aggiunto);
        verify(messaggioDao).aggiungiMessaggio(msg);

        // Trova
        when(messaggioDao.trovaTutti()).thenReturn(List.of(msg));
        List<Messaggio> trovati = messaggioService.trovaTutti();
        assertEquals(1, trovati.size());

        // Rimuovi
        doNothing().when(messaggioDao).rimuoviMessaggio(msg);
        messaggioService.rimuoviMessaggio(msg);
        verify(messaggioDao).rimuoviMessaggio(msg);

        System.out.println("✓ Sequenza completa eseguita con successo");
    }

    @Test
    public void testBranchCoverageAggiungiMessaggio() {
        System.out.println("\n=== Test 26: Branch coverage aggiungiMessaggio ===");

        // Branch 1: messaggio != null
        Messaggio msg = new Messaggio();
        when(messaggioDao.aggiungiMessaggio(msg)).thenReturn(msg);
        Messaggio result1 = messaggioService.aggiungiMessaggio(msg);
        assertNotNull(result1);
        verify(messaggioDao, times(1)).aggiungiMessaggio(msg);

        // Branch 2: messaggio == null
        Messaggio result2 = messaggioService.aggiungiMessaggio(null);
        assertNull(result2);
        verify(messaggioDao, times(1)).aggiungiMessaggio(any()); // solo 1 volta, non 2

        System.out.println("✓ Entrambi i branch di aggiungiMessaggio coperti");
    }

    @Test
    public void testBranchCoverageRimuoviMessaggio() {
        System.out.println("\n=== Test 27: Branch coverage rimuoviMessaggio ===");

        // Branch 1: messaggio != null
        Messaggio msg = new Messaggio();
        doNothing().when(messaggioDao).rimuoviMessaggio(msg);
        messaggioService.rimuoviMessaggio(msg);
        verify(messaggioDao, times(1)).rimuoviMessaggio(msg);

        // Branch 2: messaggio == null
        messaggioService.rimuoviMessaggio(null);
        verify(messaggioDao, times(1)).rimuoviMessaggio(any()); // solo 1 volta

        System.out.println("✓ Entrambi i branch di rimuoviMessaggio coperti");
    }
}
