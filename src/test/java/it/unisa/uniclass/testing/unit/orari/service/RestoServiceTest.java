package it.unisa.uniclass.testing.unit.orari.service;

import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.model.Resto;
import it.unisa.uniclass.orari.service.RestoService;
import it.unisa.uniclass.orari.service.dao.RestoRemote;
import jakarta.persistence.NoResultException;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class RestoServiceTest {

    @Mock
    private RestoRemote restoDao;

    @InjectMocks
    private RestoService service;

    @Test
    @DisplayName("Trova Resto per ID: Branch Coverage Try-Catch")
    void testTrovaRestoById() {
        Resto r = new Resto();
        when(restoDao.trovaResto(1L)).thenReturn(r);
        assertSame(r, service.trovaResto(1L));

        when(restoDao.trovaResto(2L)).thenThrow(new NoResultException());
        assertNull(service.trovaResto(2L));
    }

    @Test
    @DisplayName("Trova Resto Nome Corso (Object): Branch Coverage Try-Catch")
    void testTrovaRestoNomeCorso_Object() {
        CorsoLaurea cl = new CorsoLaurea();
        Resto r = new Resto();
        when(restoDao.trovaRestoNomeCorso("R0", cl)).thenReturn(r);
        assertSame(r, service.trovaRestoNomeCorso("R0", cl));

        when(restoDao.trovaRestoNomeCorso("RX", cl)).thenThrow(new NoResultException());
        assertNull(service.trovaRestoNomeCorso("RX", cl));
    }

    @Test
    @DisplayName("Trova Resto Nome Corso (String): Branch Coverage Try-Catch")
    void testTrovaRestoNomeCorso_String() {
        Resto r = new Resto();
        when(restoDao.trovaRestoNomeCorso("R0", "Info")).thenReturn(r);
        assertSame(r, service.trovaRestoNomeCorso("R0", "Info"));

        when(restoDao.trovaRestoNomeCorso("R0", "Error")).thenThrow(new NoResultException());
        assertNull(service.trovaRestoNomeCorso("R0", "Error"));
    }

    @Test
    @DisplayName("Aggiungi Resto: Branch Coverage Null Check")
    void testAggiungiResto() {
        // Ramo if (resto != null) -> TRUE
        Resto r = new Resto();
        service.aggiungiResto(r);
        verify(restoDao).aggiungiResto(r);

        // Ramo if (resto != null) -> FALSE
        service.aggiungiResto(null);
        verify(restoDao, times(1)).aggiungiResto(any()); // Chiamato solo una volta (quella sopra)
    }

    @Test
    @DisplayName("Rimuovi Resto: Branch Coverage Null Check")
    void testRimuoviResto() {
        Resto r = new Resto();
        service.rimuoviResto(r);
        verify(restoDao).rimuoviResto(r);

        service.rimuoviResto(null);
        verify(restoDao, times(1)).rimuoviResto(any());
    }

    @Test
    @DisplayName("Test deleghe semplici")
    void testDeleghe() {
        CorsoLaurea cl = new CorsoLaurea();
        service.trovaRestiCorsoLaurea(cl);
        service.trovaRestiCorsoLaurea("Info");
        service.trovaResto("R1");

        verify(restoDao).trovaResto("R1");
        verify(restoDao).trovaRestiCorsoLaurea("Info");
        verify(restoDao).trovaRestiCorsoLaurea(cl);
    }
}
