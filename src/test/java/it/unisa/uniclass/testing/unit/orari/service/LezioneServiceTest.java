package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.Giorno;
import it.unisa.uniclass.orari.model.Lezione;
import it.unisa.uniclass.orari.service.LezioneService;
import it.unisa.uniclass.orari.service.dao.LezioneRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Nested;
import org.mockito.Mock;
import org.mockito.MockedConstruction;
import org.mockito.MockitoAnnotations;

import javax.naming.InitialContext;
import javax.naming.NamingException;
import java.sql.Time;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test d'unità per la classe LezioneService.
 * Verifica i metodi di servizio per la gestione delle lezioni.
 */
@DisplayName("Test per la classe LezioneService")
public class LezioneServiceTest {

    @Mock
    private LezioneRemote lezioneDao;

    private LezioneService lezioneService;
    private Lezione lezione;

    @BeforeEach
    void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);

        // Usa il costruttore con iniezione diretta per i test
        lezioneService = new LezioneService(lezioneDao);

        lezione = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                             Giorno.LUNEDI, null, null, null);
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            LezioneRemote mockDao = mock(LezioneRemote.class);
            LezioneService service = new LezioneService(mockDao);

            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore JNDI fallisce quando InitialContext non è disponibile")
        void testCostruttoreJndiFallisce() {
            // Questo test verifica che il costruttore lanci un'eccezione quando JNDI non è disponibile
            // In ambiente di test normale, JNDI non è disponibile
            assertThrows(RuntimeException.class, () -> {
                new LezioneService();
            });
        }

        @Test
        @DisplayName("Costruttore JNDI funziona con InitialContext mockato")
        void testCostruttoreJndiConMock() throws Exception {
            // Mocka InitialContext usando MockedConstruction
            try (MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                    (mock, context) -> {
                        // Configura il mock per restituire il DAO mockato
                        when(mock.lookup("java:global/UniClass-Dependability/LezioneDAO"))
                                .thenReturn(lezioneDao);
                    })) {

                // Crea il service usando il costruttore JNDI
                LezioneService service = new LezioneService();

                // Verifica che il service sia stato creato
                assertNotNull(service);

                // Verifica che lookup sia stato chiamato
                InitialContext mockCtx = mockedContext.constructed().get(0);
                verify(mockCtx, times(1)).lookup("java:global/UniClass-Dependability/LezioneDAO");
            }
        }

        @Test
        @DisplayName("Costruttore JNDI lancia RuntimeException quando lookup fallisce")
        void testCostruttoreJndiLookupFallisce() throws Exception {
            // Mocka InitialContext per lanciare NamingException
            try (MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                    (mock, context) -> {
                        when(mock.lookup(anyString()))
                                .thenThrow(new NamingException("DAO non trovato"));
                    })) {

                // Verifica che il costruttore lanci RuntimeException
                RuntimeException exception = assertThrows(RuntimeException.class, () -> {
                    new LezioneService();
                });

                // Verifica il messaggio dell'eccezione
                assertTrue(exception.getMessage().contains("Errore durante il lookup di LezioneDAO"));

                // Verifica che la causa sia NamingException
                assertInstanceOf(NamingException.class, exception.getCause());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezione")
    class TrovaLezioneTest {

        @Test
        @DisplayName("trovaLezione restituisce lezione per ID valido")
        void testTrovaLezioneSuccesso() {
            long id = 1;

            when(lezioneDao.trovaLezione(id))
                    .thenReturn(lezione);

            Lezione result = lezioneService.trovaLezione(id);

            assertNotNull(result);
            assertEquals(1, result.getSemestre());
            verify(lezioneDao, times(1)).trovaLezione(id);
        }

        @Test
        @DisplayName("trovaLezione restituisce null quando lezione non trovata")
        void testTrovaLezioneNonTrovata() {
            long id = 999;

            when(lezioneDao.trovaLezione(id))
                    .thenThrow(new NoResultException("Lezione non trovata"));

            Lezione result = lezioneService.trovaLezione(id);

            assertNull(result);
            verify(lezioneDao, times(1)).trovaLezione(id);
        }

        @Test
        @DisplayName("trovaLezione con ID diversi")
        void testTrovaLezioneIdDiversi() {
            for (long id = 1; id <= 3; id++) {
                Lezione lezTest = new Lezione((int)id, Time.valueOf("09:00:00"),
                                             Time.valueOf("11:00:00"), Giorno.LUNEDI, null, null, null);

                when(lezioneDao.trovaLezione(id))
                        .thenReturn(lezTest);

                Lezione result = lezioneService.trovaLezione(id);

                assertNotNull(result);
                assertEquals(id, result.getSemestre());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniCorso")
    class TrovaLezioniCorsoTest {

        @Test
        @DisplayName("trovaLezioniCorso restituisce lezioni per corso")
        void testTrovaLezioniCorsoSuccesso() {
            String nomeCorso = "Programmazione I";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniCorso(nomeCorso))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniCorso(nomeCorso);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniCorso(nomeCorso);
        }

        @Test
        @DisplayName("trovaLezioniCorso restituisce lista vuota")
        void testTrovaLezioniCorsoVuoto() {
            String nomeCorso = "Corso Inesistente";

            when(lezioneDao.trovaLezioniCorso(nomeCorso))
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaLezioniCorso(nomeCorso);

            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaLezioniCorso con corsi diversi")
        void testTrovaLezioniCorsoDiversi() {
            String[] corsi = {"Programmazione I", "Algoritmi", "Basi di Dati"};

            for (String nome : corsi) {
                List<Lezione> lezioni = new ArrayList<>();
                lezioni.add(lezione);

                when(lezioneDao.trovaLezioniCorso(nome))
                        .thenReturn(lezioni);

                List<Lezione> result = lezioneService.trovaLezioniCorso(nome);

                assertEquals(1, result.size());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniOre")
    class TrovaLezioniOreTest {

        @Test
        @DisplayName("trovaLezioniOre restituisce lezioni per fascia oraria")
        void testTrovaLezioniOreSuccesso() {
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniOre(oraInizio, oraFine))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniOre(oraInizio, oraFine);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniOre(oraInizio, oraFine);
        }

        @Test
        @DisplayName("trovaLezioniOre restituisce lista vuota")
        void testTrovaLezioniOreVuoto() {
            Time oraInizio = Time.valueOf("23:00:00");
            Time oraFine = Time.valueOf("23:30:00");

            when(lezioneDao.trovaLezioniOre(oraInizio, oraFine))
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaLezioniOre(oraInizio, oraFine);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniOreGiorno")
    class TrovaLezioniOreGiornoTest {

        @Test
        @DisplayName("trovaLezioniOreGiorno restituisce lezioni per fascia oraria e giorno")
        void testTrovaLezioniOreGiornoSuccesso() {
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");
            Giorno giorno = Giorno.LUNEDI;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniOreGiorno(oraInizio, oraFine, giorno))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniOreGiorno(oraInizio, oraFine, giorno);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniOreGiorno(oraInizio, oraFine, giorno);
        }

        @Test
        @DisplayName("trovaLezioniOreGiorno con giorni diversi")
        void testTrovaLezioniOreGiornoDiversi() {
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");

            for (Giorno giorno : new Giorno[]{Giorno.LUNEDI, Giorno.MARTEDI, Giorno.MERCOLEDI}) {
                when(lezioneDao.trovaLezioniOreGiorno(oraInizio, oraFine, giorno))
                        .thenReturn(new ArrayList<>());

                List<Lezione> result = lezioneService.trovaLezioniOreGiorno(oraInizio, oraFine, giorno);

                assertNotNull(result);
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniAule")
    class TrovaLezioniAuleTest {

        @Test
        @DisplayName("trovaLezioniAule restituisce lezioni per aula")
        void testTrovaLezioniAuleSuccesso() {
            String nome = "Aula 101";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniAule(nome))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniAule(nome);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniAule(nome);
        }

        @Test
        @DisplayName("trovaLezioniAule restituisce lista vuota")
        void testTrovaLezioniAuleVuoto() {
            String nome = "Aula Inesistente";

            when(lezioneDao.trovaLezioniAule(nome))
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaLezioniAule(nome);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTutte")
    class TrovaTutteTest {

        @Test
        @DisplayName("trovaTutte restituisce lista di tutte le lezioni")
        void testTrovaTutteSuccesso() {
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);
            lezioni.add(new Lezione(2, Time.valueOf("14:00:00"), Time.valueOf("16:00:00"),
                                   Giorno.MARTEDI, null, null, null));

            when(lezioneDao.trovaTutte())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaTutte();

            assertNotNull(result);
            assertEquals(2, result.size());
            verify(lezioneDao, times(1)).trovaTutte();
        }

        @Test
        @DisplayName("trovaTutte restituisce lista vuota")
        void testTrovaTutteVuoto() {
            when(lezioneDao.trovaTutte())
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaTutte();

            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutte con molte lezioni")
        void testTrovaTutteMolte() {
            List<Lezione> lezioni = new ArrayList<>();
            for (int i = 1; i <= 30; i++) {
                lezioni.add(new Lezione(i, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                                       Giorno.LUNEDI, null, null, null));
            }

            when(lezioneDao.trovaTutte())
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaTutte();

            assertEquals(30, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniCorsoLaureaRestoAnno")
    class TrovaLezioniCorsoLaureaRestoAnnoTest {

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnno restituisce lezioni")
        void testTrovaLezioniCorsoLaureaRestoAnnoSuccesso() {
            long clid = 1, reid = 1;
            int anid = 1;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniCorsoLaureaRestoAnno(clid, reid, anid))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniCorsoLaureaRestoAnno(clid, reid, anid);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniCorsoLaureaRestoAnno(clid, reid, anid);
        }

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnno restituisce lista vuota")
        void testTrovaLezioniCorsoLaureaRestoAnnoVuoto() {
            when(lezioneDao.trovaLezioniCorsoLaureaRestoAnno(999, 999, 999))
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaLezioniCorsoLaureaRestoAnno(999, 999, 999);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniCorsoLaureaRestoAnnoSemestre")
    class TrovaLezioniCorsoLaureaRestoAnnoSemestreTest {

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnnoSemestre restituisce lezioni")
        void testTrovaLezioniCorsoLaureaRestoAnnoSemestreSuccesso() {
            long clid = 1, reid = 1;
            int anid = 1, semestre = 1;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniCorsoLaureaRestoAnnoSemestre(clid, reid, anid, semestre))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniCorsoLaureaRestoAnnoSemestre(clid, reid, anid, semestre);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniCorsoLaureaRestoAnnoSemestre(clid, reid, anid, semestre);
        }

        @Test
        @DisplayName("trovaLezioniCorsoLaureaRestoAnnoSemestre con semestri diversi")
        void testTrovaLezioniCorsoLaureaRestoAnnoSemestreDiversi() {
            for (int semestre = 1; semestre <= 2; semestre++) {
                when(lezioneDao.trovaLezioniCorsoLaureaRestoAnnoSemestre(1, 1, 1, semestre))
                        .thenReturn(new ArrayList<>());

                List<Lezione> result = lezioneService.trovaLezioniCorsoLaureaRestoAnnoSemestre(1, 1, 1, semestre);

                assertNotNull(result);
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaLezioniDocente")
    class TrovaLezioniDocenteTest {

        @Test
        @DisplayName("trovaLezioniDocente restituisce lezioni per docente")
        void testTrovaLezioniDocenteSuccesso() {
            String nomeDocente = "Prof. Rossi";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniDocente(nomeDocente))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniDocente(nomeDocente);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(lezioneDao, times(1)).trovaLezioniDocente(nomeDocente);
        }

        @Test
        @DisplayName("trovaLezioniDocente restituisce lista vuota")
        void testTrovaLezioniDocenteVuoto() {
            String nomeDocente = "Prof. Inesistente";

            when(lezioneDao.trovaLezioniDocente(nomeDocente))
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaLezioniDocente(nomeDocente);

            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiLezione")
    class AggiungiLezioneTest {

        @Test
        @DisplayName("aggiungiLezione aggiunge correttamente una lezione")
        void testAggiungiLezioneSuccesso() {
            lezioneService.aggiungiLezione(lezione);

            verify(lezioneDao, times(1)).aggiungiLezione(lezione);
        }

        @Test
        @DisplayName("aggiungiLezione aggiunge multiple lezioni")
        void testAggiungiLezioneMultiple() {
            for (int i = 1; i <= 3; i++) {
                Lezione lezTest = new Lezione(i, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                                             Giorno.LUNEDI, null, null, null);

                lezioneService.aggiungiLezione(lezTest);

                verify(lezioneDao, times(1)).aggiungiLezione(lezTest);
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviLezione")
    class RimuoviLezioneTest {

        @Test
        @DisplayName("rimuoviLezione rimuove correttamente una lezione")
        void testRimuoviLezioneSuccesso() {
            lezioneService.rimuoviLezione(lezione);

            verify(lezioneDao, times(1)).rimuoviLezione(lezione);
        }

        @Test
        @DisplayName("rimuoviLezione rimuove multiple lezioni")
        void testRimuoviLezioneMultiple() {
            for (int i = 1; i <= 3; i++) {
                Lezione lezTest = new Lezione(i, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                                             Giorno.LUNEDI, null, null, null);

                lezioneService.rimuoviLezione(lezTest);

                verify(lezioneDao, times(1)).rimuoviLezione(lezTest);
            }
        }
    }

    @Nested
    @DisplayName("Test di gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        @DisplayName("trovaLezione gestisce eccezioni")
        void testTrovaLezioneEccezione() {
            long id = -1;

            when(lezioneDao.trovaLezione(id))
                    .thenThrow(new NoResultException("Not found"));

            Lezione result = lezioneService.trovaLezione(id);

            assertNull(result);
            verify(lezioneDao, times(1)).trovaLezione(id);
        }

        @Test
        @DisplayName("trovaLezioniCorso gestisce eccezioni")
        void testTrovaLezioniCorsoEccezione() {
            String nome = "";

            when(lezioneDao.trovaLezioniCorso(nome))
                    .thenReturn(new ArrayList<>());

            List<Lezione> result = lezioneService.trovaLezioniCorso(nome);

            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutte gestisce eccezioni")
        void testTrovaTutteEccezione() {
            when(lezioneDao.trovaTutte())
                    .thenThrow(new RuntimeException("Database error"));

            assertThrows(RuntimeException.class, () -> lezioneService.trovaTutte());
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            // Aggiungi
            lezioneService.aggiungiLezione(lezione);
            verify(lezioneDao, times(1)).aggiungiLezione(lezione);

            // Trova
            when(lezioneDao.trovaLezione(1L))
                    .thenReturn(lezione);
            Lezione result = lezioneService.trovaLezione(1L);
            assertNotNull(result);

            // Rimuovi
            lezioneService.rimuoviLezione(lezione);
            verify(lezioneDao, atLeastOnce()).rimuoviLezione(lezione);
        }

        @Test
        @DisplayName("Ricerca per corso e modifica")
        void testRicercaCorsoEModifica() {
            String nomeCorso = "Programmazione I";
            List<Lezione> lezioni = new ArrayList<>();
            Lezione lez1 = new Lezione(1, Time.valueOf("09:00:00"), Time.valueOf("11:00:00"),
                                      Giorno.LUNEDI, null, null, null);
            lezioni.add(lez1);

            when(lezioneDao.trovaLezioniCorso(nomeCorso))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniCorso(nomeCorso);
            assertEquals(1, result.size());

            result.getFirst().setSemestre(2);
            lezioneService.aggiungiLezione(result.getFirst());

            verify(lezioneDao, times(1)).aggiungiLezione(result.getFirst());
        }

        @Test
        @DisplayName("Ricerca per fascia oraria e giorno")
        void testRicercaOreGiorno() {
            Time oraInizio = Time.valueOf("09:00:00");
            Time oraFine = Time.valueOf("11:00:00");
            Giorno giorno = Giorno.LUNEDI;
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniOreGiorno(oraInizio, oraFine, giorno))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniOreGiorno(oraInizio, oraFine, giorno);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("Ricerca per docente e aggiornamento")
        void testRicercaDocenteEAggiornamento() {
            String nomeDocente = "Prof. Rossi";
            List<Lezione> lezioni = new ArrayList<>();
            lezioni.add(lezione);

            when(lezioneDao.trovaLezioniDocente(nomeDocente))
                    .thenReturn(lezioni);

            List<Lezione> result = lezioneService.trovaLezioniDocente(nomeDocente);
            assertNotNull(result);

            lezioneService.aggiungiLezione(result.getFirst());
            verify(lezioneDao, times(1)).aggiungiLezione(result.getFirst());
        }
    }
}
