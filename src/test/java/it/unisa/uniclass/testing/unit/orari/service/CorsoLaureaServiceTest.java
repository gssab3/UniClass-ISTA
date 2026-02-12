package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote;
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
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Test d'unità per la classe CorsoLaureaService.
 * Verifica i metodi di servizio per la gestione dei corsi di laurea.
 */
@DisplayName("Test per la classe CorsoLaureaService")
public class CorsoLaureaServiceTest {

    @Mock
    private CorsoLaureaRemote corsoLaureaDAO;

    private CorsoLaureaService corsoLaureaService;
    private CorsoLaurea corsoLaurea;

    @BeforeEach
    void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);
        
        // Usa il costruttore con iniezione diretta per i test
        corsoLaureaService = new CorsoLaureaService(corsoLaureaDAO);
        
        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");
        corsoLaurea.setAnniDidattici(new ArrayList<>());
        corsoLaurea.setResti(new ArrayList<>());
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            CorsoLaureaRemote mockDao = mock(CorsoLaureaRemote.class);
            CorsoLaureaService service = new CorsoLaureaService(mockDao);
            
            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore JNDI fallisce quando InitialContext non è disponibile")
        void testCostruttoreJndiFallisce() {
            assertThrows(RuntimeException.class, () -> {
                new CorsoLaureaService();
            });
        }

        @Test
        @DisplayName("Costruttore JNDI funziona con InitialContext mockato")
        void testCostruttoreJndiConMock() throws Exception {
            try (MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                    (mock, context) -> {
                        when(mock.lookup("java:global/UniClass-Dependability/CorsoLaureaDAO!it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote"))
                                .thenReturn(corsoLaureaDAO);
                    })) {
                
                CorsoLaureaService service = new CorsoLaureaService();
                
                assertNotNull(service);
                
                InitialContext mockCtx = mockedContext.constructed().get(0);
                verify(mockCtx, times(1)).lookup("java:global/UniClass-Dependability/CorsoLaureaDAO!it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote");
            }
        }

        @Test
        @DisplayName("Costruttore JNDI lancia RuntimeException quando lookup fallisce")
        void testCostruttoreJndiLookupFallisce() throws Exception {
            try (MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                    (mock, context) -> {
                        when(mock.lookup(anyString()))
                                .thenThrow(new NamingException("DAO non trovato"));
                    })) {
                
                RuntimeException exception = assertThrows(RuntimeException.class, () -> {
                    new CorsoLaureaService();
                });
                
                assertTrue(exception.getMessage().contains("Errore durante il lookup di CorsoLaureaDAO"));
                assertInstanceOf(NamingException.class, exception.getCause());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaCorsoLaurea(long id)")
    class TrovaCorsoLaureaByIdTest {

        @Test
        @DisplayName("trovaCorsoLaurea restituisce corso per ID valido")
        void testTrovaCorsoLaureaByIdSuccesso() {
            long id = 1L;

            when(corsoLaureaDAO.trovaCorsoLaurea(id))
                    .thenReturn(corsoLaurea);

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(id);

            assertNotNull(result);
            assertEquals("Informatica", result.getNome());
            verify(corsoLaureaDAO, times(1)).trovaCorsoLaurea(id);
        }

        @Test
        @DisplayName("trovaCorsoLaurea restituisce null quando corso non trovato")
        void testTrovaCorsoLaureaByIdNonTrovato() {
            long id = 999L;

            when(corsoLaureaDAO.trovaCorsoLaurea(id))
                    .thenThrow(new NoResultException("Corso non trovato"));

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(id);
            
            assertNull(result);
            verify(corsoLaureaDAO, times(1)).trovaCorsoLaurea(id);
        }

        @Test
        @DisplayName("trovaCorsoLaurea con ID diversi")
        void testTrovaCorsoLaureaByIdDiversi() {
            for (long id = 1; id <= 3; id++) {
                CorsoLaurea corso = new CorsoLaurea();
                corso.setNome("Corso " + id);

                when(corsoLaureaDAO.trovaCorsoLaurea(id))
                        .thenReturn(corso);

                CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(id);

                assertNotNull(result);
                assertEquals("Corso " + id, result.getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaCorsoLaurea(String nome)")
    class TrovaCorsoLaureaByNomeTest {

        @Test
        @DisplayName("trovaCorsoLaurea restituisce corso per nome valido")
        void testTrovaCorsoLaureaByNomeSuccesso() {
            String nome = "Informatica";

            when(corsoLaureaDAO.trovaCorsoLaurea(nome))
                    .thenReturn(corsoLaurea);

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);

            assertNotNull(result);
            assertEquals(nome, result.getNome());
            verify(corsoLaureaDAO, times(1)).trovaCorsoLaurea(nome);
        }

        @Test
        @DisplayName("trovaCorsoLaurea restituisce null quando corso non trovato")
        void testTrovaCorsoLaureaByNomeNonTrovato() {
            String nome = "Corso Inesistente";

            when(corsoLaureaDAO.trovaCorsoLaurea(nome))
                    .thenThrow(new NoResultException("Corso non trovato"));

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);
            
            assertNull(result);
            verify(corsoLaureaDAO, times(1)).trovaCorsoLaurea(nome);
        }

        @Test
        @DisplayName("trovaCorsoLaurea con nomi diversi")
        void testTrovaCorsoLaureaByNomeDiversi() {
            String[] nomi = {"Informatica", "Matematica", "Fisica"};

            for (String nome : nomi) {
                CorsoLaurea corso = new CorsoLaurea();
                corso.setNome(nome);

                when(corsoLaureaDAO.trovaCorsoLaurea(nome))
                        .thenReturn(corso);

                CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);

                assertNotNull(result);
                assertEquals(nome, result.getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTutti")
    class TrovaTuttiTest {

        @Test
        @DisplayName("trovaTutti restituisce lista di tutti i corsi")
        void testTrovaTuttiSuccesso() {
            List<CorsoLaurea> corsi = new ArrayList<>();
            CorsoLaurea corso1 = new CorsoLaurea();
            corso1.setNome("Informatica");
            CorsoLaurea corso2 = new CorsoLaurea();
            corso2.setNome("Matematica");
            CorsoLaurea corso3 = new CorsoLaurea();
            corso3.setNome("Fisica");
            corsi.add(corso1);
            corsi.add(corso2);
            corsi.add(corso3);

            when(corsoLaureaDAO.trovaTutti())
                    .thenReturn(corsi);

            List<CorsoLaurea> result = corsoLaureaService.trovaTutti();

            assertNotNull(result);
            assertEquals(3, result.size());
            verify(corsoLaureaDAO, times(1)).trovaTutti();
        }

        @Test
        @DisplayName("trovaTutti restituisce lista vuota")
        void testTrovaTuttiVuoto() {
            when(corsoLaureaDAO.trovaTutti())
                    .thenReturn(new ArrayList<>());

            List<CorsoLaurea> result = corsoLaureaService.trovaTutti();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutti con molti corsi")
        void testTrovaTuttiMolti() {
            List<CorsoLaurea> corsi = new ArrayList<>();
            for (int i = 1; i <= 20; i++) {
                CorsoLaurea corso = new CorsoLaurea();
                corso.setNome("Corso " + i);
                corsi.add(corso);
            }

            when(corsoLaureaDAO.trovaTutti())
                    .thenReturn(corsi);

            List<CorsoLaurea> result = corsoLaureaService.trovaTutti();

            assertEquals(20, result.size());
        }

        @Test
        @DisplayName("trovaTutti lancia RuntimeException quando DAO fallisce")
        void testTrovaTuttiEccezione() {
            when(corsoLaureaDAO.trovaTutti())
                    .thenThrow(new RuntimeException("Errore database"));

            RuntimeException exception = assertThrows(RuntimeException.class, () -> {
                corsoLaureaService.trovaTutti();
            });

            assertTrue(exception.getMessage().contains("Errore durante il recupero dei corsi di laurea"));
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiCorsoLaurea")
    class AggiungiCorsoLaureaTest {

        @Test
        @DisplayName("aggiungiCorsoLaurea aggiunge correttamente un corso")
        void testAggiungiCorsoLaureaSuccesso() {
            corsoLaureaService.aggiungiCorsoLaurea(corsoLaurea);

            verify(corsoLaureaDAO, times(1)).aggiungiCorsoLaurea(corsoLaurea);
        }

        @Test
        @DisplayName("aggiungiCorsoLaurea aggiunge multipli corsi")
        void testAggiungiCorsoLaureaMultiple() {
            for (int i = 1; i <= 3; i++) {
                CorsoLaurea corso = new CorsoLaurea();
                corso.setNome("Corso " + i);

                corsoLaureaService.aggiungiCorsoLaurea(corso);

                verify(corsoLaureaDAO, times(1)).aggiungiCorsoLaurea(corso);
            }
        }

        @Test
        @DisplayName("aggiungiCorsoLaurea aggiorna un corso esistente")
        void testAggiungiCorsoLaureaAggiorna() {
            CorsoLaurea corsoAggiornato = new CorsoLaurea();
            corsoAggiornato.setNome("Informatica Magistrale");

            corsoLaureaService.aggiungiCorsoLaurea(corsoAggiornato);

            verify(corsoLaureaDAO, times(1)).aggiungiCorsoLaurea(corsoAggiornato);
        }

        @Test
        @DisplayName("aggiungiCorsoLaurea lancia IllegalArgumentException per corso null")
        void testAggiungiCorsoLaureaNull() {
            IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
                corsoLaureaService.aggiungiCorsoLaurea(null);
            });

            assertTrue(exception.getMessage().contains("nome valido"));
        }

        @Test
        @DisplayName("aggiungiCorsoLaurea lancia IllegalArgumentException per nome null")
        void testAggiungiCorsoLaureaNomeNull() {
            CorsoLaurea corsoSenzaNome = new CorsoLaurea();
            corsoSenzaNome.setNome(null);

            IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
                corsoLaureaService.aggiungiCorsoLaurea(corsoSenzaNome);
            });

            assertTrue(exception.getMessage().contains("nome valido"));
        }

        @Test
        @DisplayName("aggiungiCorsoLaurea lancia IllegalArgumentException per nome vuoto")
        void testAggiungiCorsoLaureaNomeVuoto() {
            CorsoLaurea corsoNomeVuoto = new CorsoLaurea();
            corsoNomeVuoto.setNome("");

            IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
                corsoLaureaService.aggiungiCorsoLaurea(corsoNomeVuoto);
            });

            assertTrue(exception.getMessage().contains("nome valido"));
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviCorsoLaurea")
    class RimuoviCorsoLaureaTest {

        @Test
        @DisplayName("rimuoviCorsoLaurea rimuove correttamente un corso")
        void testRimuoviCorsoLaureaSuccesso() {
            corsoLaureaService.rimuoviCorsoLaurea(corsoLaurea);

            verify(corsoLaureaDAO, times(1)).rimuoviCorsoLaurea(corsoLaurea);
        }

        @Test
        @DisplayName("rimuoviCorsoLaurea rimuove multipli corsi")
        void testRimuoviCorsoLaureaMultiple() {
            for (int i = 1; i <= 3; i++) {
                CorsoLaurea corso = new CorsoLaurea();
                corso.setNome("Corso " + i);

                corsoLaureaService.rimuoviCorsoLaurea(corso);

                verify(corsoLaureaDAO, times(1)).rimuoviCorsoLaurea(corso);
            }
        }

        @Test
        @DisplayName("rimuoviCorsoLaurea lancia IllegalArgumentException per corso null")
        void testRimuoviCorsoLaureaNull() {
            IllegalArgumentException exception = assertThrows(IllegalArgumentException.class, () -> {
                corsoLaureaService.rimuoviCorsoLaurea(null);
            });

            assertTrue(exception.getMessage().contains("non può essere null"));
        }
    }

    @Nested
    @DisplayName("Test di gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        @DisplayName("trovaCorsoLaurea(long) gestisce NoResultException")
        void testTrovaCorsoLaureaByIdEccezione() {
            long id = -1;

            when(corsoLaureaDAO.trovaCorsoLaurea(id))
                    .thenThrow(new NoResultException("Not found"));

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(id);
            
            assertNull(result);
            verify(corsoLaureaDAO, times(1)).trovaCorsoLaurea(id);
        }

        @Test
        @DisplayName("trovaCorsoLaurea(String) gestisce NoResultException")
        void testTrovaCorsoLaureaByNomeEccezione() {
            String nome = "";

            when(corsoLaureaDAO.trovaCorsoLaurea(nome))
                    .thenThrow(new NoResultException("Not found"));

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);
            
            assertNull(result);
            verify(corsoLaureaDAO, times(1)).trovaCorsoLaurea(nome);
        }

        @Test
        @DisplayName("trovaTutti propaga RuntimeException")
        void testTrovaTuttiPropagaEccezione() {
            when(corsoLaureaDAO.trovaTutti())
                    .thenThrow(new RuntimeException("Database error"));

            assertThrows(RuntimeException.class, () -> {
                corsoLaureaService.trovaTutti();
            });
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            // Aggiungi
            corsoLaureaService.aggiungiCorsoLaurea(corsoLaurea);
            verify(corsoLaureaDAO, times(1)).aggiungiCorsoLaurea(corsoLaurea);

            // Trova per ID
            when(corsoLaureaDAO.trovaCorsoLaurea(1L))
                    .thenReturn(corsoLaurea);
            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(1L);
            assertNotNull(result);

            // Rimuovi
            corsoLaureaService.rimuoviCorsoLaurea(corsoLaurea);
            verify(corsoLaureaDAO, atLeastOnce()).rimuoviCorsoLaurea(corsoLaurea);
        }

        @Test
        @DisplayName("Ricerca per nome e aggiornamento")
        void testRicercaNomeEAggiornamento() {
            String nome = "Informatica";

            when(corsoLaureaDAO.trovaCorsoLaurea(nome))
                    .thenReturn(corsoLaurea);

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);
            assertNotNull(result);
            assertEquals(nome, result.getNome());

            result.setNome("Informatica Magistrale");
            corsoLaureaService.aggiungiCorsoLaurea(result);

            verify(corsoLaureaDAO, times(1)).aggiungiCorsoLaurea(result);
        }

        @Test
        @DisplayName("Recupero tutti i corsi e rimozione")
        void testRecuperoTuttiERimozione() {
            List<CorsoLaurea> corsi = new ArrayList<>();
            corsi.add(corsoLaurea);

            when(corsoLaureaDAO.trovaTutti())
                    .thenReturn(corsi);

            List<CorsoLaurea> result = corsoLaureaService.trovaTutti();
            assertEquals(1, result.size());

            corsoLaureaService.rimuoviCorsoLaurea(result.get(0));
            verify(corsoLaureaDAO, times(1)).rimuoviCorsoLaurea(result.get(0));
        }
    }
}

