package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.RestoService;
import it.unisa.uniclass.orari.service.dao.RestoRemote;
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

@DisplayName("Test per la classe RestoService")
public class RestoServiceTest {

    @Mock
    private RestoRemote restoDao;

    private RestoService restoService;
    private Resto resto;
    private CorsoLaurea corsoLaurea;

    @BeforeEach
    void setUp() {
        MockitoAnnotations.openMocks(this);

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
        @DisplayName("Costruttore senza parametri crea comunque l'istanza")
        void testCostruttoreVuoto() {
            RestoService service = new RestoService();
            assertNotNull(service);
        }
    }

    @Nested
    @DisplayName("Test trovaRestiCorsoLaurea(CorsoLaurea)")
    class TrovaRestiCorsoLaureaByObjectTest {

        @Test
        void testSuccesso() {
            when(restoDao.trovaRestiCorsoLaurea(corsoLaurea))
                    .thenReturn(List.of(resto));

            List<Resto> result = restoService.trovaRestiCorsoLaurea(corsoLaurea);

            assertEquals(1, result.size());
        }

        @Test
        void testVuoto() {
            when(restoDao.trovaRestiCorsoLaurea(corsoLaurea))
                    .thenReturn(new ArrayList<>());

            assertTrue(restoService.trovaRestiCorsoLaurea(corsoLaurea).isEmpty());
        }
    }

    @Nested
    @DisplayName("Test trovaRestiCorsoLaurea(String)")
    class TrovaRestiCorsoLaureaByStringTest {

        @Test
        void testSuccesso() {
            when(restoDao.trovaRestiCorsoLaurea("Ingegneria Informatica"))
                    .thenReturn(List.of(resto));

            List<Resto> result = restoService.trovaRestiCorsoLaurea("Ingegneria Informatica");

            assertEquals(1, result.size());
        }
    }

    @Nested
    @DisplayName("Test trovaResto(String)")
    class TrovaRestoByStringTest {

        @Test
        void testSuccesso() {
            when(restoDao.trovaResto("Resto 0"))
                    .thenReturn(List.of(resto));

            List<Resto> result = restoService.trovaResto("Resto 0");

            assertEquals(1, result.size());
        }
    }

    @Nested
    @DisplayName("Test trovaResto(long)")
    class TrovaRestoByIdTest {

        @Test
        void testSuccesso() {
            when(restoDao.trovaResto(1L)).thenReturn(resto);

            Resto result = restoService.trovaResto(1L);

            assertNotNull(result);
        }

        @Test
        void testNonTrovato() {
            when(restoDao.trovaResto(999L)).thenThrow(new NoResultException());

            assertNull(restoService.trovaResto(999L));
        }
    }

    @Nested
    @DisplayName("Test trovaRestoNomeCorso")
    class TrovaRestoNomeCorsoTest {

        @Test
        void testByObjectSuccesso() {
            when(restoDao.trovaRestoNomeCorso("Resto 0", corsoLaurea))
                    .thenReturn(resto);

            assertNotNull(restoService.trovaRestoNomeCorso("Resto 0", corsoLaurea));
        }

        @Test
        void testByStringSuccesso() {
            when(restoDao.trovaRestoNomeCorso("Resto 0", "Ingegneria Informatica"))
                    .thenReturn(resto);

            assertNotNull(restoService.trovaRestoNomeCorso("Resto 0", "Ingegneria Informatica"));
        }
    }

    @Nested
    @DisplayName("Test aggiungiResto")
    class AggiungiRestoTest {

        @Test
        void testSuccesso() {
            restoService.aggiungiResto(resto);
            verify(restoDao).aggiungiResto(resto);
        }

        @Test
        void testNull() {
            restoService.aggiungiResto(null);
            verify(restoDao, never()).aggiungiResto(any());
        }
    }

    @Nested
    @DisplayName("Test rimuoviResto")
    class RimuoviRestoTest {

        @Test
        void testSuccesso() {
            restoService.rimuoviResto(resto);
            verify(restoDao).rimuoviResto(resto);
        }

        @Test
        void testNull() {
            restoService.rimuoviResto(null);
            verify(restoDao, never()).rimuoviResto(any());
        }
    }

    @Nested
    @DisplayName("Test gestione eccezioni")
    class GestioneEccezioniTest {

        @Test
        void testTrovaRestoByIdEccezione() {
            when(restoDao.trovaResto(-1L)).thenThrow(new NoResultException());
            assertNull(restoService.trovaResto(-1L));
        }
    }
}
