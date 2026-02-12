package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.RestoService;
import it.unisa.uniclass.orari.service.dao.RestoRemote;
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
 * Test d'unità per la classe RestoService.
 * Verifica i metodi di servizio per la gestione dei resti.
 */
@DisplayName("Test per la classe RestoService")
public class RestoServiceTest {

    @Mock
    private RestoRemote restoDao;

    private RestoService restoService;
    private Resto resto;
    private CorsoLaurea corsoLaurea;

    @BeforeEach
    void setUp() throws Exception {
        MockitoAnnotations.openMocks(this);

        // Usa il costruttore con iniezione diretta per i test
        restoService = new RestoService(restoDao);

        corsoLaurea = new CorsoLaurea("Ingegneria Informatica");
        resto = new Resto();
        resto.setNome("Resto 0");
        resto.setCorsoLaurea(corsoLaurea);
    }

    @Nested
    @DisplayName("Test dei costruttori")
    class CostruttoriTest {

        @Test
        @DisplayName("Costruttore con parametro inietta correttamente il DAO")
        void testCostruttoreConParametro() {
            RestoRemote mockDao = mock(RestoRemote.class);
            RestoService service = new RestoService(mockDao);

            assertNotNull(service);
        }

        @Test
        @DisplayName("Costruttore JNDI fallisce quando InitialContext non è disponibile")
        void testCostruttoreJndiFallisce() {
            assertThrows(RuntimeException.class, () -> {
                new RestoService();
            });
        }

        @Test
        @DisplayName("Costruttore JNDI funziona con InitialContext mockato")
        void testCostruttoreJndiConMock() throws Exception {
            try (MockedConstruction<InitialContext> mockedContext = mockConstruction(InitialContext.class,
                    (mock, context) -> {
                        when(mock.lookup("java:global/UniClass-Dependability/RestoDAO"))
                                .thenReturn(restoDao);
                    })) {

                RestoService service = new RestoService();

                assertNotNull(service);

                InitialContext mockCtx = mockedContext.constructed().get(0);
                verify(mockCtx, times(1)).lookup("java:global/UniClass-Dependability/RestoDAO");
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
                    new RestoService();
                });

                assertTrue(exception.getMessage().contains("Errore durante il lookup di RestoDAO"));
                assertInstanceOf(NamingException.class, exception.getCause());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaRestiCorsoLaurea(CorsoLaurea)")
    class TrovaRestiCorsoLaureaByObjectTest {

        @Test
        @DisplayName("trovaRestiCorsoLaurea restituisce resti per corso di laurea")
        void testTrovaRestiCorsoLaureaByObjectSuccesso() {
            List<Resto> resti = new ArrayList<>();
            resti.add(resto);

            when(restoDao.trovaRestiCorsoLaurea(corsoLaurea))
                    .thenReturn(resti);

            List<Resto> result = restoService.trovaRestiCorsoLaurea(corsoLaurea);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(restoDao, times(1)).trovaRestiCorsoLaurea(corsoLaurea);
        }

        @Test
        @DisplayName("trovaRestiCorsoLaurea restituisce lista vuota")
        void testTrovaRestiCorsoLaureaByObjectVuoto() {
            when(restoDao.trovaRestiCorsoLaurea(corsoLaurea))
                    .thenReturn(new ArrayList<>());

            List<Resto> result = restoService.trovaRestiCorsoLaurea(corsoLaurea);

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaRestiCorsoLaurea con multipli resti")
        void testTrovaRestiCorsoLaureaByObjectMultipli() {
            List<Resto> resti = new ArrayList<>();
            for (int i = 0; i < 3; i++) {
                Resto restoTest = new Resto();
                restoTest.setNome("Resto " + i);
                resti.add(restoTest);
            }

            when(restoDao.trovaRestiCorsoLaurea(corsoLaurea))
                    .thenReturn(resti);

            List<Resto> result = restoService.trovaRestiCorsoLaurea(corsoLaurea);

            assertEquals(3, result.size());
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaRestiCorsoLaurea(String)")
    class TrovaRestiCorsoLaureaByStringTest {

        @Test
        @DisplayName("trovaRestiCorsoLaurea restituisce resti per nome corso di laurea")
        void testTrovaRestiCorsoLaureaByStringSuccesso() {
            String nomeCorso = "Ingegneria Informatica";
            List<Resto> resti = new ArrayList<>();
            resti.add(resto);
            resti.add(resto);

            when(restoDao.trovaRestiCorsoLaurea(nomeCorso))
                    .thenReturn(resti);

            List<Resto> result = restoService.trovaRestiCorsoLaurea(nomeCorso);

            assertNotNull(result);
            assertEquals(2, result.size());
            verify(restoDao, times(1)).trovaRestiCorsoLaurea(nomeCorso);
        }

        @Test
        @DisplayName("trovaRestiCorsoLaurea restituisce lista vuota per nome")
        void testTrovaRestiCorsoLaureaByStringVuoto() {
            when(restoDao.trovaRestiCorsoLaurea("Corso Inesistente"))
                    .thenReturn(new ArrayList<>());

            List<Resto> result = restoService.trovaRestiCorsoLaurea("Corso Inesistente");

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaRestiCorsoLaurea con corsi di laurea diversi")
        void testTrovaRestiCorsoLaureaDiversi() {
            String[] corsi = {"Ingegneria Informatica", "Ingegneria Gestionale", "Ingegneria Civile"};

            for (String nome : corsi) {
                List<Resto> resti = new ArrayList<>();
                resti.add(resto);

                when(restoDao.trovaRestiCorsoLaurea(nome))
                        .thenReturn(resti);

                List<Resto> result = restoService.trovaRestiCorsoLaurea(nome);

                assertEquals(1, result.size());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaResto(String)")
    class TrovaRestoByStringTest {

        @Test
        @DisplayName("trovaResto restituisce resti per nome")
        void testTrovaRestoByStringSuccesso() {
            String nomeResto = "Resto 0";
            List<Resto> resti = new ArrayList<>();
            resti.add(resto);

            when(restoDao.trovaResto(nomeResto))
                    .thenReturn(resti);

            List<Resto> result = restoService.trovaResto(nomeResto);

            assertNotNull(result);
            assertEquals(1, result.size());
            verify(restoDao, times(1)).trovaResto(nomeResto);
        }

        @Test
        @DisplayName("trovaResto restituisce lista vuota")
        void testTrovaRestoByStringVuoto() {
            when(restoDao.trovaResto("Resto Inesistente"))
                    .thenReturn(new ArrayList<>());

            List<Resto> result = restoService.trovaResto("Resto Inesistente");

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("trovaResto con nomi diversi")
        void testTrovaRestoByStringDiversi() {
            String[] nomi = {"Resto 0", "Resto 1", "Resto 2"};

            for (String nome : nomi) {
                Resto restoTest = new Resto();
                restoTest.setNome(nome);

                when(restoDao.trovaResto(nome))
                        .thenReturn(new ArrayList<>(java.util.List.of(restoTest)));

                List<Resto> result = restoService.trovaResto(nome);

                assertEquals(1, result.size());
                assertEquals(nome, result.get(0).getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaResto(long id)")
    class TrovaRestoByIdTest {

        @Test
        @DisplayName("trovaResto restituisce resto per ID valido")
        void testTrovaRestoByIdSuccesso() {
            long id = 1;

            when(restoDao.trovaResto(id))
                    .thenReturn(resto);

            Resto result = restoService.trovaResto(id);

            assertNotNull(result);
            assertEquals("Resto 0", result.getNome());
            verify(restoDao, times(1)).trovaResto(id);
        }

        @Test
        @DisplayName("trovaResto restituisce null quando resto non trovato")
        void testTrovaRestoByIdNonTrovato() {
            long id = 999;

            when(restoDao.trovaResto(id))
                    .thenThrow(new NoResultException("Resto non trovato"));

            Resto result = restoService.trovaResto(id);

            assertNull(result);
            verify(restoDao, times(1)).trovaResto(id);
        }

        @Test
        @DisplayName("trovaResto con ID diversi")
        void testTrovaRestoByIdDiversi() {
            for (long id = 1; id <= 3; id++) {
                Resto restoTest = new Resto();
                restoTest.setNome("Resto " + id);

                when(restoDao.trovaResto(id))
                        .thenReturn(restoTest);

                Resto result = restoService.trovaResto(id);

                assertNotNull(result);
                assertEquals("Resto " + id, result.getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaRestoNomeCorso(String, CorsoLaurea)")
    class TrovaRestoNomeCorsoByObjectTest {

        @Test
        @DisplayName("trovaRestoNomeCorso restituisce resto per nome e corso")
        void testTrovaRestoNomeCorsoByObjectSuccesso() {
            String nomeResto = "Resto 0";

            when(restoDao.trovaRestoNomeCorso(nomeResto, corsoLaurea))
                    .thenReturn(resto);

            Resto result = restoService.trovaRestoNomeCorso(nomeResto, corsoLaurea);

            assertNotNull(result);
            assertEquals(nomeResto, result.getNome());
            verify(restoDao, times(1)).trovaRestoNomeCorso(nomeResto, corsoLaurea);
        }

        @Test
        @DisplayName("trovaRestoNomeCorso restituisce null quando non trovato")
        void testTrovaRestoNomeCorsoByObjectNonTrovato() {
            String nomeResto = "Resto Inesistente";

            when(restoDao.trovaRestoNomeCorso(nomeResto, corsoLaurea))
                    .thenThrow(new NoResultException("Resto non trovato"));

            Resto result = restoService.trovaRestoNomeCorso(nomeResto, corsoLaurea);

            assertNull(result);
            verify(restoDao, times(1)).trovaRestoNomeCorso(nomeResto, corsoLaurea);
        }

        @Test
        @DisplayName("trovaRestoNomeCorso con parametri diversi")
        void testTrovaRestoNomeCorsoByObjectDiversi() {
            String[] nomi = {"Resto 0", "Resto 1", "Resto 2"};

            for (String nome : nomi) {
                Resto restoTest = new Resto();
                restoTest.setNome(nome);

                when(restoDao.trovaRestoNomeCorso(nome, corsoLaurea))
                        .thenReturn(restoTest);

                Resto result = restoService.trovaRestoNomeCorso(nome, corsoLaurea);

                assertEquals(nome, result.getNome());
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo trovaRestoNomeCorso(String, String)")
    class TrovaRestoNomeCorsoByStringTest {

        @Test
        @DisplayName("trovaRestoNomeCorso restituisce resto per nome resto e nome corso")
        void testTrovaRestoNomeCorsoByStringSuccesso() {
            String nomeResto = "Resto 0";
            String nomeCorso = "Ingegneria Informatica";

            when(restoDao.trovaRestoNomeCorso(nomeResto, nomeCorso))
                    .thenReturn(resto);

            Resto result = restoService.trovaRestoNomeCorso(nomeResto, nomeCorso);

            assertNotNull(result);
            assertEquals(nomeResto, result.getNome());
            verify(restoDao, times(1)).trovaRestoNomeCorso(nomeResto, nomeCorso);
        }

        @Test
        @DisplayName("trovaRestoNomeCorso restituisce null quando non trovato")
        void testTrovaRestoNomeCorsoByStringNonTrovato() {
            when(restoDao.trovaRestoNomeCorso("Inesistente", "Inesistente"))
                    .thenThrow(new NoResultException("Resto non trovato"));

            Resto result = restoService.trovaRestoNomeCorso("Inesistente", "Inesistente");

            assertNull(result);
            verify(restoDao, times(1)).trovaRestoNomeCorso("Inesistente", "Inesistente");
        }

        @Test
        @DisplayName("trovaRestoNomeCorso con combinazioni diverse")
        void testTrovaRestoNomeCorsoByStringDiversi() {
            String[] nomiResti = {"Resto 0", "Resto 1", "Resto 2"};
            String[] nomiCorsi = {"Ingegneria Informatica", "Ingegneria Gestionale"};

            for (String nomeResto : nomiResti) {
                for (String nomeCorso : nomiCorsi) {
                    Resto restoTest = new Resto();
                    restoTest.setNome(nomeResto);

                    when(restoDao.trovaRestoNomeCorso(nomeResto, nomeCorso))
                            .thenReturn(restoTest);

                    Resto result = restoService.trovaRestoNomeCorso(nomeResto, nomeCorso);

                    assertEquals(nomeResto, result.getNome());
                }
            }
        }
    }

    @Nested
    @DisplayName("Test del metodo aggiungiResto")
    class AggiungiRestoTest {

        @Test
        @DisplayName("aggiungiResto aggiunge correttamente un resto")
        void testAggiungiRestoSuccesso() {
            restoService.aggiungiResto(resto);

            verify(restoDao, times(1)).aggiungiResto(resto);
        }

        @Test
        @DisplayName("aggiungiResto aggiunge multipli resti")
        void testAggiungiRestoMultipli() {
            for (int i = 1; i <= 5; i++) {
                Resto restoTest = new Resto();
                restoTest.setNome("Resto " + i);

                restoService.aggiungiResto(restoTest);

                verify(restoDao, times(1)).aggiungiResto(restoTest);
            }
        }

        @Test
        @DisplayName("aggiungiResto aggiorna un resto esistente")
        void testAggiungiRestoAggiorna() {
            Resto restoModificato = new Resto();
            restoModificato.setNome("Resto Modificato");

            restoService.aggiungiResto(restoModificato);

            verify(restoDao, times(1)).aggiungiResto(restoModificato);
        }

        @Test
        @DisplayName("aggiungiResto non fa nulla con resto null")
        void testAggiungiRestoNull() {
            restoService.aggiungiResto(null);

            verify(restoDao, never()).aggiungiResto(any());
        }
    }

    @Nested
    @DisplayName("Test del metodo rimuoviResto")
    class RimuoviRestoTest {

        @Test
        @DisplayName("rimuoviResto rimuove correttamente un resto")
        void testRimuoviRestoSuccesso() {
            restoService.rimuoviResto(resto);

            verify(restoDao, times(1)).rimuoviResto(resto);
        }

        @Test
        @DisplayName("rimuoviResto rimuove multipli resti")
        void testRimuoviRestoMultipli() {
            for (int i = 1; i <= 5; i++) {
                Resto restoTest = new Resto();
                restoTest.setNome("Resto " + i);

                restoService.rimuoviResto(restoTest);

                verify(restoDao, times(1)).rimuoviResto(restoTest);
            }
        }

        @Test
        @DisplayName("rimuoviResto non fa nulla con resto null")
        void testRimuoviRestoNull() {
            restoService.rimuoviResto(null);

            verify(restoDao, never()).rimuoviResto(any());
        }
    }

    @Nested
    @DisplayName("Test di gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        @DisplayName("trovaResto per ID gestisce NoResultException")
        void testTrovaRestoByIdEccezione() {
            long id = -1;

            when(restoDao.trovaResto(id))
                    .thenThrow(new NoResultException("Not found"));

            Resto result = restoService.trovaResto(id);

            assertNull(result);
            verify(restoDao, times(1)).trovaResto(id);
        }

        @Test
        @DisplayName("trovaRestoNomeCorso (CorsoLaurea) gestisce NoResultException")
        void testTrovaRestoNomeCorsoByObjectEccezione() {
            when(restoDao.trovaRestoNomeCorso("", corsoLaurea))
                    .thenThrow(new NoResultException("Not found"));

            Resto result = restoService.trovaRestoNomeCorso("", corsoLaurea);

            assertNull(result);
        }

        @Test
        @DisplayName("trovaRestoNomeCorso (String) gestisce NoResultException")
        void testTrovaRestoNomeCorsoByStringEccezione() {
            when(restoDao.trovaRestoNomeCorso("", ""))
                    .thenThrow(new NoResultException("Not found"));

            Resto result = restoService.trovaRestoNomeCorso("", "");

            assertNull(result);
        }

        @Test
        @DisplayName("trovaRestiCorsoLaurea (Object) gestisce liste vuote")
        void testTrovaRestiCorsoLaureaByObjectListaVuota() {
            when(restoDao.trovaRestiCorsoLaurea(new CorsoLaurea()))
                    .thenReturn(new ArrayList<>());

            List<Resto> result = restoService.trovaRestiCorsoLaurea(new CorsoLaurea());

            assertNotNull(result);
            assertTrue(result.isEmpty());
        }
    }

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            // Aggiungi
            restoService.aggiungiResto(resto);
            verify(restoDao, times(1)).aggiungiResto(resto);

            // Trova per ID
            when(restoDao.trovaResto(1L))
                    .thenReturn(resto);
            Resto result = restoService.trovaResto(1L);
            assertNotNull(result);

            // Rimuovi
            restoService.rimuoviResto(resto);
            verify(restoDao, atLeastOnce()).rimuoviResto(resto);
        }

        @Test
        @DisplayName("Ricerca per corso di laurea e modifica")
        void testRicercaCorsoLaureaEModifica() {
            String nomeCorso = "Ingegneria Informatica";
            List<Resto> resti = new ArrayList<>();
            Resto resto1 = new Resto();
            resto1.setNome("Resto 0");
            resti.add(resto1);

            when(restoDao.trovaRestiCorsoLaurea(nomeCorso))
                    .thenReturn(resti);

            List<Resto> result = restoService.trovaRestiCorsoLaurea(nomeCorso);
            assertEquals(1, result.size());

            result.get(0).setNome("Resto Modificato");
            restoService.aggiungiResto(result.get(0));

            verify(restoDao, times(1)).aggiungiResto(result.get(0));
        }

        @Test
        @DisplayName("Ricerca per nome e aggiornamento")
        void testRicercaNomeEAggiornamento() {
            String nomeResto = "Resto 0";

            when(restoDao.trovaResto(nomeResto))
                    .thenReturn(new ArrayList<>(java.util.List.of(resto)));

            List<Resto> result = restoService.trovaResto(nomeResto);
            assertNotNull(result);

            result.get(0).setNome("Resto Aggiornato");
            restoService.aggiungiResto(result.get(0));

            verify(restoDao, times(1)).aggiungiResto(result.get(0));
        }

        @Test
        @DisplayName("Ricerca per nome corso di laurea e nome resto")
        void testRicercaNomeCorsoENomeResto() {
            String nomeResto = "Resto 0";
            String nomeCorso = "Ingegneria Informatica";

            when(restoDao.trovaRestoNomeCorso(nomeResto, nomeCorso))
                    .thenReturn(resto);

            Resto result = restoService.trovaRestoNomeCorso(nomeResto, nomeCorso);
            assertNotNull(result);
            assertEquals(nomeResto, result.getNome());

            restoService.aggiungiResto(result);
            verify(restoDao, times(1)).aggiungiResto(result);
        }

        @Test
        @DisplayName("Operazioni con parametri null non causano errori")
        void testOperazioniConNull() {
            // Aggiungi null
            restoService.aggiungiResto(null);
            verify(restoDao, never()).aggiungiResto(any());

            // Rimuovi null
            restoService.rimuoviResto(null);
            verify(restoDao, never()).rimuoviResto(any());
        }
    }
}

