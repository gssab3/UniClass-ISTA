package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.orari.service.dao.CorsoLaureaRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.mockito.Mock;
import org.mockito.MockitoAnnotations;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@DisplayName("Test per la classe CorsoLaureaService")
public class CorsoLaureaServiceTest {

    @Mock
    private CorsoLaureaRemote corsoLaureaDAO;

    private CorsoLaureaService corsoLaureaService;
    private CorsoLaurea corsoLaurea;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);
        corsoLaureaService = new CorsoLaureaService(corsoLaureaDAO);

        corsoLaurea = new CorsoLaurea();
        corsoLaurea.setNome("Informatica");
        corsoLaurea.setAnniDidattici(new ArrayList<>());
        corsoLaurea.setResti(new ArrayList<>());
    }

    // ---------------------------------------------------------
    // COSTRUTTORI
    // ---------------------------------------------------------

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
        @DisplayName("Costruttore senza parametri crea comunque l'istanza")
        void testCostruttoreVuoto() {
            CorsoLaureaService service = new CorsoLaureaService();
            assertNotNull(service);
        }
    }

    // ---------------------------------------------------------
    // TROVA PER ID
    // ---------------------------------------------------------

    @Nested
    @DisplayName("Test del metodo trovaCorsoLaurea(long id)")
    class TrovaCorsoLaureaByIdTest {

        @Test
        @DisplayName("Restituisce corso per ID valido")
        void testTrovaCorsoLaureaByIdSuccesso() {
            long id = 1L;

            when(corsoLaureaDAO.trovaCorsoLaurea(id)).thenReturn(corsoLaurea);

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(id);

            assertNotNull(result);
            assertEquals("Informatica", result.getNome());
            verify(corsoLaureaDAO).trovaCorsoLaurea(id);
        }

        @Test
        @DisplayName("Restituisce null quando non trovato")
        void testTrovaCorsoLaureaByIdNonTrovato() {
            long id = 999L;

            when(corsoLaureaDAO.trovaCorsoLaurea(id)).thenThrow(new NoResultException());

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(id);

            assertNull(result);
            verify(corsoLaureaDAO).trovaCorsoLaurea(id);
        }
    }

    // ---------------------------------------------------------
    // TROVA PER NOME
    // ---------------------------------------------------------

    @Nested
    @DisplayName("Test del metodo trovaCorsoLaurea(String nome)")
    class TrovaCorsoLaureaByNomeTest {

        @Test
        @DisplayName("Restituisce corso per nome valido")
        void testTrovaCorsoLaureaByNomeSuccesso() {
            String nome = "Informatica";

            when(corsoLaureaDAO.trovaCorsoLaurea(nome)).thenReturn(corsoLaurea);

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);

            assertNotNull(result);
            assertEquals(nome, result.getNome());
            verify(corsoLaureaDAO).trovaCorsoLaurea(nome);
        }

        @Test
        @DisplayName("Restituisce null quando non trovato")
        void testTrovaCorsoLaureaByNomeNonTrovato() {
            String nome = "Corso Inesistente";

            when(corsoLaureaDAO.trovaCorsoLaurea(nome)).thenThrow(new NoResultException());

            CorsoLaurea result = corsoLaureaService.trovaCorsoLaurea(nome);

            assertNull(result);
            verify(corsoLaureaDAO).trovaCorsoLaurea(nome);
        }
    }

    // ---------------------------------------------------------
    // TROVA TUTTI
    // ---------------------------------------------------------

    @Nested
    @DisplayName("Test del metodo trovaTutti")
    class TrovaTuttiTest {

        @Test
        @DisplayName("Restituisce lista completa")
        void testTrovaTuttiSuccesso() {
            List<CorsoLaurea> corsi = new ArrayList<>();
            corsi.add(new CorsoLaurea());
            corsi.add(new CorsoLaurea());

            when(corsoLaureaDAO.trovaTutti()).thenReturn(corsi);

            List<CorsoLaurea> result = corsoLaureaService.trovaTutti();

            assertEquals(2, result.size());
            verify(corsoLaureaDAO).trovaTutti();
        }

        @Test
        @DisplayName("Restituisce lista vuota")
        void testTrovaTuttiVuoto() {
            when(corsoLaureaDAO.trovaTutti()).thenReturn(new ArrayList<>());

            List<CorsoLaurea> result = corsoLaureaService.trovaTutti();

            assertTrue(result.isEmpty());
        }

        @Test
        @DisplayName("Propaga RuntimeException")
        void testTrovaTuttiPropagaEccezione() {
            when(corsoLaureaDAO.trovaTutti()).thenThrow(new RuntimeException("Errore DB"));

            assertThrows(RuntimeException.class, () -> corsoLaureaService.trovaTutti());
        }
    }

    // ---------------------------------------------------------
    // AGGIUNGI CORSO
    // ---------------------------------------------------------

    @Nested
    @DisplayName("Test del metodo aggiungiCorsoLaurea")
    class AggiungiCorsoLaureaTest {

        @Test
        @DisplayName("Aggiunge correttamente")
        void testAggiungiCorsoLaureaSuccesso() {
            corsoLaureaService.aggiungiCorsoLaurea(corsoLaurea);
            verify(corsoLaureaDAO).aggiungiCorsoLaurea(corsoLaurea);
        }

        @Test
        @DisplayName("Lancia eccezione per null")
        void testAggiungiCorsoLaureaNull() {
            assertThrows(IllegalArgumentException.class, () -> corsoLaureaService.aggiungiCorsoLaurea(null));
        }

        @Test
        @DisplayName("Lancia eccezione per nome null")
        void testAggiungiCorsoLaureaNomeNull() {
            CorsoLaurea c = new CorsoLaurea();
            c.setNome(null);

            assertThrows(IllegalArgumentException.class, () -> corsoLaureaService.aggiungiCorsoLaurea(c));
        }

        @Test
        @DisplayName("Lancia eccezione per nome vuoto")
        void testAggiungiCorsoLaureaNomeVuoto() {
            CorsoLaurea c = new CorsoLaurea();
            c.setNome("");

            assertThrows(IllegalArgumentException.class, () -> corsoLaureaService.aggiungiCorsoLaurea(c));
        }
    }

    // ---------------------------------------------------------
    // RIMUOVI CORSO
    // ---------------------------------------------------------

    @Nested
    @DisplayName("Test del metodo rimuoviCorsoLaurea")
    class RimuoviCorsoLaureaTest {

        @Test
        @DisplayName("Rimuove correttamente")
        void testRimuoviCorsoLaureaSuccesso() {
            corsoLaureaService.rimuoviCorsoLaurea(corsoLaurea);
            verify(corsoLaureaDAO).rimuoviCorsoLaurea(corsoLaurea);
        }

        @Test
        @DisplayName("Lancia eccezione per null")
        void testRimuoviCorsoLaureaNull() {
            assertThrows(IllegalArgumentException.class, () -> corsoLaureaService.rimuoviCorsoLaurea(null));
        }
    }

    // ---------------------------------------------------------
    // SCENARI COMPLESSI
    // ---------------------------------------------------------

    @Nested
    @DisplayName("Test di integrazione")
    class ScenariComplessiTest {

        @Test
        @DisplayName("Sequenza completa con operazioni multiple")
        void testSequenzaCompleta() {
            corsoLaureaService.aggiungiCorsoLaurea(corsoLaurea);
            verify(corsoLaureaDAO).aggiungiCorsoLaurea(corsoLaurea);

            when(corsoLaureaDAO.trovaCorsoLaurea(1L)).thenReturn(corsoLaurea);
            assertNotNull(corsoLaureaService.trovaCorsoLaurea(1L));

            corsoLaureaService.rimuoviCorsoLaurea(corsoLaurea);
            verify(corsoLaureaDAO).rimuoviCorsoLaurea(corsoLaurea);
        }
    }
}
