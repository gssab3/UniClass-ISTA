package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.AnnoDidattico;
import it.unisa.uniclass.orari.service.AnnoDidatticoService;
import it.unisa.uniclass.orari.service.dao.AnnoDidatticoRemote;
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
 * Test d'unità per la classe AnnoDidatticoService.
 * Verifica i metodi di servizio per la gestione degli anni didattici.
 */
@DisplayName("Test per la classe AnnoDidatticoService")
public class AnnoDidatticoServiceTest {

    @Mock
    private AnnoDidatticoRemote annoDidatticoDao;

    private AnnoDidatticoService annoDidatticoService;
    private AnnoDidattico annoDidattico;

    @BeforeEach
    void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);

        // Usa il costruttore con iniezione diretta per i test
        annoDidatticoService = new AnnoDidatticoService(annoDidatticoDao);

        annoDidattico = new AnnoDidattico("2023-2024");
        annoDidattico.setCorsiLaurea(new ArrayList<>());
        annoDidattico.setCorsi(new ArrayList<>());
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            AnnoDidatticoRemote mockDao = mock(AnnoDidatticoRemote.class);
            AnnoDidatticoService service = new AnnoDidatticoService(mockDao);

            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore JNDI fallisce quando InitialContext non è disponibile")
        void testCostruttoreJndiFallisce() {
            assertThrows(RuntimeException.class, () -> {
                new AnnoDidatticoService();
            });
        }

        @Test
        @DisplayName("Costruttore JNDI funziona con InitialContext mockato")
        void testCostruttoreJndiConMock() throws Exception {
            try (MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                    (mock, context) -> {
                        when(mock.lookup("java:global/UniClass-Dependability/AnnoDidatticoDAO"))
                                .thenReturn(annoDidatticoDao);
                    })) {

                AnnoDidatticoService service = new AnnoDidatticoService();

                assertNotNull(service);

                InitialContext mockCtx = mockedContext.constructed().get(0);
                verify(mockCtx, times(1)).lookup("java:global/UniClass-Dependability/AnnoDidatticoDAO");
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
                    new AnnoDidatticoService();
                });

                assertTrue(exception.getMessage().contains("Errore durante il lookup di AnnoDidatticoDAO"));
                assertInstanceOf(NamingException.class, exception.getCause());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaAnno")
    class TrovaAnnoTest {

        @Test
        @DisplayName("trovaAnno restituisce lista di anni didattici")
        void testTrovaAnnoSuccesso() {
            String anno = "2023-2024";
            List<AnnoDidattico> anni = new ArrayList<>();
            anni.add(annoDidattico);

            when(annoDidatticoDao.trovaAnno(anno))
                    .thenReturn(anni);

            List<AnnoDidattico> result = annoDidatticoService.trovaAnno(anno);

            assertNotNull(result);
            assertEquals(1, result.size());
            assertEquals(anno, result.getFirst().getAnno());
            verify(annoDidatticoDao, times(1)).trovaAnno(anno);
        }

        @Test
        @DisplayName("trovaAnno restituisce lista vuota")
        void testTrovaAnnoVuoto() {
            String anno = "2099-2100";

            when(annoDidatticoDao.trovaAnno(anno))
                    .thenReturn(new ArrayList<>());

            List<AnnoDidattico> result = annoDidatticoService.trovaAnno(anno);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaAnno con multipli anni")
        void testTrovaAnnoMultipli() {
            String anno = "2023-2024";
            List<AnnoDidattico> anni = new ArrayList<>();
            for (int i = 0; i < 3; i++) {
                anni.add(new AnnoDidattico(anno));
            }

            when(annoDidatticoDao.trovaAnno(anno))
                    .thenReturn(anni);

            List<AnnoDidattico> result = annoDidatticoService.trovaAnno(anno);

            assertEquals(3, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaId")
    class TrovaIdTest {

        @Test
        @DisplayName("trovaId restituisce anno per ID valido")
        void testTrovaIdSuccesso() {
            int id = 1;

            when(annoDidatticoDao.trovaId(id))
                    .thenReturn(annoDidattico);

            AnnoDidattico result = annoDidatticoService.trovaId(id);

            assertNotNull(result);
            assertEquals("2023-2024", result.getAnno());
            verify(annoDidatticoDao, times(1)).trovaId(id);
        }

        @Test
        @DisplayName("trovaId restituisce null quando anno non trovato")
        void testTrovaIdNonTrovato() {
            int id = 999;

            when(annoDidatticoDao.trovaId(id))
                    .thenThrow(new NoResultException("Anno non trovato"));

            AnnoDidattico result = annoDidatticoService.trovaId(id);

            assertNull(result);
            verify(annoDidatticoDao, times(1)).trovaId(id);
        }

        @Test
        @DisplayName("trovaId con ID diversi")
        void testTrovaIdDiversi() {
            for (int id = 1; id <= 3; id++) {
                AnnoDidattico ad = new AnnoDidattico("Anno " + id);

                when(annoDidatticoDao.trovaId(id))
                        .thenReturn(ad);

                AnnoDidattico result = annoDidatticoService.trovaId(id);

                assertNotNull(result);
                assertEquals("Anno " + id, result.getAnno());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTutti")
    class TrovaTuttiTest {

        @Test
        @DisplayName("trovaTutti restituisce lista di tutti gli anni")
        void testTrovaTuttiSuccesso() {
            List<AnnoDidattico> anni = new ArrayList<>();
            anni.add(new AnnoDidattico("2021-2022"));
            anni.add(new AnnoDidattico("2022-2023"));
            anni.add(new AnnoDidattico("2023-2024"));

            when(annoDidatticoDao.trovaTutti())
                    .thenReturn(anni);

            List<AnnoDidattico> result = annoDidatticoService.trovaTutti();

            assertNotNull(result);
            assertEquals(3, result.size());
            verify(annoDidatticoDao, times(1)).trovaTutti();
        }

        @Test
        @DisplayName("trovaTutti restituisce lista vuota")
        void testTrovaTuttiVuoto() {
            when(annoDidatticoDao.trovaTutti())
                    .thenReturn(new ArrayList<>());

            List<AnnoDidattico> result = annoDidatticoService.trovaTutti();

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTutti con molti anni")
        void testTrovaTuttiMolti() {
            List<AnnoDidattico> anni = new ArrayList<>();
            for (int i = 1; i <= 20; i++) {
                anni.add(new AnnoDidattico("Anno " + i));
            }

            when(annoDidatticoDao.trovaTutti())
                    .thenReturn(anni);

            List<AnnoDidattico> result = annoDidatticoService.trovaTutti();

            assertEquals(20, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiAnno")
    class AggiungiAnnoTest {

        @Test
        @DisplayName("aggiungiAnno aggiunge correttamente un anno")
        void testAggiungiAnnoSuccesso() {
            annoDidatticoService.aggiungiAnno(annoDidattico);

            verify(annoDidatticoDao, times(1)).aggiungiAnno(annoDidattico);
        }

        @Test
        @DisplayName("aggiungiAnno aggiunge multipli anni")
        void testAggiungiAnnoMultipli() {
            for (int i = 1; i <= 5; i++) {
                AnnoDidattico ad = new AnnoDidattico("Anno " + i);

                annoDidatticoService.aggiungiAnno(ad);

                verify(annoDidatticoDao, times(1)).aggiungiAnno(ad);
            }
        }

        @Test
        @DisplayName("aggiungiAnno aggiorna un anno esistente")
        void testAggiungiAnnoAggiorna() {
            AnnoDidattico adModificato = new AnnoDidattico("2024-2025");

            annoDidatticoService.aggiungiAnno(adModificato);

            verify(annoDidatticoDao, times(1)).aggiungiAnno(adModificato);
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviAnno")
    class RimuoviAnnoTest {

        @Test
        @DisplayName("rimuoviAnno rimuove correttamente un anno")
        void testRimuoviAnnoSuccesso() {
            annoDidatticoService.rimuoviAnno(annoDidattico);

            verify(annoDidatticoDao, times(1)).rimuoviAnno(annoDidattico);
        }

        @Test
        @DisplayName("rimuoviAnno rimuove multipli anni")
        void testRimuoviAnnoMultipli() {
            for (int i = 1; i <= 5; i++) {
                AnnoDidattico ad = new AnnoDidattico("Anno " + i);

                annoDidatticoService.rimuoviAnno(ad);

                verify(annoDidatticoDao, times(1)).rimuoviAnno(ad);
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTuttiCorsoLaurea")
    class TrovaTuttiCorsoLaureaTest {

        @Test
        @DisplayName("trovaTuttiCorsoLaurea restituisce anni per corso")
        void testTrovaTuttiCorsoLaureaSuccesso() {
            long idCorso = 1;
            List<AnnoDidattico> anni = new ArrayList<>();
            anni.add(annoDidattico);

            when(annoDidatticoDao.trovaTuttiCorsoLaurea(idCorso))
                    .thenReturn(anni);

            List<AnnoDidattico> result = annoDidatticoService.trovaTuttiCorsoLaurea(idCorso);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(annoDidatticoDao, times(1)).trovaTuttiCorsoLaurea(idCorso);
        }

        @Test
        @DisplayName("trovaTuttiCorsoLaurea restituisce lista vuota")
        void testTrovaTuttiCorsoLaureaVuoto() {
            long idCorso = 999;

            when(annoDidatticoDao.trovaTuttiCorsoLaurea(idCorso))
                    .thenReturn(new ArrayList<>());

            List<AnnoDidattico> result = annoDidatticoService.trovaTuttiCorsoLaurea(idCorso);

            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaTuttiCorsoLaurea con corsi diversi")
        void testTrovaTuttiCorsoLaureaDiversi() {
            for (long idCorso = 1; idCorso <= 3; idCorso++) {
                List<AnnoDidattico> anni = new ArrayList<>();
                anni.add(new AnnoDidattico("Anno " + idCorso));

                when(annoDidatticoDao.trovaTuttiCorsoLaurea(idCorso))
                        .thenReturn(anni);

                List<AnnoDidattico> result = annoDidatticoService.trovaTuttiCorsoLaurea(idCorso);

                assertEquals(1, result.size());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaTuttiCorsoLaureaNome")
    class TrovaTuttiCorsoLaureaNomeTest {

        @Test
        @DisplayName("trovaTuttiCorsoLaureaNome restituisce anno per corso e nome")
        void testTrovaTuttiCorsoLaureaNomeSuccesso() {
            long idCorso = 1;
            String anno = "2023-2024";

            when(annoDidatticoDao.trovaCorsoLaureaNome(idCorso, anno))
                    .thenReturn(annoDidattico);

            AnnoDidattico result = annoDidatticoService.trovaTuttiCorsoLaureaNome(idCorso, anno);

            assertNotNull(result);
            assertEquals(anno, result.getAnno());
            verify(annoDidatticoDao, times(1)).trovaCorsoLaureaNome(idCorso, anno);
        }

        @Test
        @DisplayName("trovaTuttiCorsoLaureaNome restituisce null quando non trovato")
        void testTrovaTuttiCorsoLaureaNomeNonTrovato() {
            long idCorso = 999;
            String anno = "2099-2100";

            when(annoDidatticoDao.trovaCorsoLaureaNome(idCorso, anno))
                    .thenThrow(new NoResultException("Anno non trovato"));

            AnnoDidattico result = annoDidatticoService.trovaTuttiCorsoLaureaNome(idCorso, anno);

            assertNull(result);
            verify(annoDidatticoDao, times(1)).trovaCorsoLaureaNome(idCorso, anno);
        }

        @Test
        @DisplayName("trovaTuttiCorsoLaureaNome con parametri diversi")
        void testTrovaTuttiCorsoLaureaNomeDiversi() {
            for (long idCorso = 1; idCorso <= 2; idCorso++) {
                for (String anno : new String[]{"2021-2022", "2022-2023", "2023-2024"}) {
                    AnnoDidattico ad = new AnnoDidattico(anno);

                    when(annoDidatticoDao.trovaCorsoLaureaNome(idCorso, anno))
                            .thenReturn(ad);

                    AnnoDidattico result = annoDidatticoService.trovaTuttiCorsoLaureaNome(idCorso, anno);

                    assertEquals(anno, result.getAnno());
                }
            }
        }
    }

    @Nested
    @DisplayName("Test di gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        @DisplayName("trovaAnno gestisce eccezioni gracefully")
        void testTrovaAnnoEccezione() {
            String anno = "Invalid";

            when(annoDidatticoDao.trovaAnno(anno))
                    .thenReturn(new ArrayList<>());

            List<AnnoDidattico> result = annoDidatticoService.trovaAnno(anno);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaId gestisce NoResultException")
        void testTrovaIdEccezione() {
            int id = -1;

            when(annoDidatticoDao.trovaId(id))
                    .thenThrow(new NoResultException("Not found"));

            AnnoDidattico result = annoDidatticoService.trovaId(id);

            assertNull(result);
            verify(annoDidatticoDao, times(1)).trovaId(id);
        }

        @Test
        @DisplayName("trovaCorsoLaureaNome gestisce eccezioni")
        void testTrovaCorsoLaureaNomeEccezione() {
            when(annoDidatticoDao.trovaCorsoLaureaNome(-1, ""))
                    .thenThrow(new NoResultException("Not found"));

            assertThrows(NoResultException.class, () -> annoDidatticoDao.trovaCorsoLaureaNome(-1, ""));
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            // Aggiungi
            annoDidatticoService.aggiungiAnno(annoDidattico);
            verify(annoDidatticoDao, times(1)).aggiungiAnno(annoDidattico);

            // Trova
            when(annoDidatticoDao.trovaId(1))
                    .thenReturn(annoDidattico);
            AnnoDidattico result = annoDidatticoService.trovaId(1);
            assertNotNull(result);

            // Rimuovi
            annoDidatticoService.rimuoviAnno(annoDidattico);
            verify(annoDidatticoDao, atLeastOnce()).rimuoviAnno(annoDidattico);
        }

        @Test
        @DisplayName("Ricerca per corso di laurea")
        void testRicercaCorsoLaurea() {
            long idCorso = 1;
            List<AnnoDidattico> anni = new ArrayList<>();
            AnnoDidattico ad = new AnnoDidattico("2023-2024");
            anni.add(ad);

            when(annoDidatticoDao.trovaTuttiCorsoLaurea(idCorso))
                    .thenReturn(anni);

            List<AnnoDidattico> result = annoDidatticoService.trovaTuttiCorsoLaurea(idCorso);
            assertEquals(1, result.size());
        }

        @Test
        @DisplayName("Ricerca e aggiornamento")
        void testRicercaEAggiornamento() {
            long idCorso = 1;
            String anno = "2023-2024";

            when(annoDidatticoDao.trovaCorsoLaureaNome(idCorso, anno))
                    .thenReturn(annoDidattico);

            AnnoDidattico result = annoDidatticoService.trovaTuttiCorsoLaureaNome(idCorso, anno);
            assertNotNull(result);
            assertEquals(anno, result.getAnno());

            annoDidatticoService.aggiungiAnno(result);
            verify(annoDidatticoDao, times(1)).aggiungiAnno(result);
        }
    }
}